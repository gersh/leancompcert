import LeanCompCert.Ports.ArraySegMobiusRootStore

/-! # Root prime-table address composition -/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- A set collection gate selects the live table cursor rather than the
scratch sink. -/
theorem postRootAddress_collect (c : Cfg) (idx : Nat) (s : AState)
    (write sink : Nat)
    (h137 : s.regs 137 = 1)
    (hWrite : s.regs rWrite = write)
    (hSink : c.primeSink = sink)
    (hsinkM : sink < M)
    (hwriteM : write < M) :
    (arun idx s (postRootAddress c)).regs 141 = write := by
  have hwriteMod : write % M = write := Nat.mod_eq_of_lt hwriteM
  have hsinkMod : sink % M = sink := Nat.mod_eq_of_lt hsinkM
  have h137' : s.regs 137 = 1 := h137
  have hWrite' : s.regs 129 = write := by simpa [rWrite] using hWrite
  have h1mod : (1 : Nat) % M = 1 := by decide
  have hMPos : 0 < M := by decide
  have hnegOne : 1 + (M - 1) = M := by omega
  simp [postRootAddress, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, denoteOp, AState.writeReg, rWrite,
    h137', hWrite', hSink, hsinkMod, hwriteMod, h1mod, hnegOne]

end LeanCompCert.Ports.ArraySegMobiusMark

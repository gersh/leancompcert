import LeanCompCert.Ports.ArraySegMobiusCursorPrefix

/-!
# Root/main selector of the production segmented sieve

The first seven instructions choose the prime-table cursor limit.  This file
proves the exact root and main values while framing all persistent cursor
registers and the array.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- In the main phase the selector installs the complete table length. -/
theorem selectorBlock_limit_main (c : Cfg) (idx : Nat) (s : AState)
    (hmain : c.rootSpan ≤ idx)
    (hidxM : idx < M)
    (hrootM : c.rootSpan < M)
    (hKM : c.tableLen < M) :
    let q := arun idx s (selectorBlock c)
    q.regs rLimit = c.tableLen ∧ q.regs rPi = s.regs rPi ∧
      q.regs rP = s.regs rP ∧ q.regs rJ = s.regs rJ ∧
      q.regs rR = s.regs rR ∧ q.regs rW = s.regs rW ∧
      q.arr = s.arr := by
  have hidxMod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hrootMod : c.rootSpan % M = c.rootSpan := Nat.mod_eq_of_lt hrootM
  have hKMod : c.tableLen % M = c.tableLen := Nat.mod_eq_of_lt hKM
  have hnot : ¬idx % M < c.rootSpan % M := by
    rw [hidxMod, hrootMod]
    omega
  simp [selectorBlock, Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rR, rW, rLimit,
    hnot, hKMod]

/-- In the root phase the selector restricts marking to the bootstrap table. -/
theorem selectorBlock_limit_root (c : Cfg) (idx : Nat) (s : AState)
    (hroot : idx < c.rootSpan)
    (hidxM : idx < M)
    (hrootM : c.rootSpan < M)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (hKM : c.tableLen < M) :
    let q := arun idx s (selectorBlock c)
    q.regs rLimit = c.bootCount ∧ q.regs rPi = s.regs rPi ∧
      q.regs rP = s.regs rP ∧ q.regs rJ = s.regs rJ ∧
      q.regs rR = s.regs rR ∧ q.regs rW = s.regs rW ∧
      q.arr = s.arr := by
  have hidxMod : idx % M = idx := Nat.mod_eq_of_lt hidxM
  have hrootMod : c.rootSpan % M = c.rootSpan := Nat.mod_eq_of_lt hrootM
  have hKMod : c.tableLen % M = c.tableLen := Nat.mod_eq_of_lt hKM
  have hdiffM : c.tableLen - c.bootCount < M := by omega
  have hdiffMod : (c.tableLen - c.bootCount) % M =
      c.tableLen - c.bootCount := Nat.mod_eq_of_lt hdiffM
  have hlt : idx % M < c.rootSpan % M := by
    rw [hidxMod, hrootMod]
    exact hroot
  have hsubRaw :
      (c.tableLen + (M - (c.tableLen - c.bootCount))) % M =
        c.bootCount := by
    have hsplit :
        c.tableLen + (M - (c.tableLen - c.bootCount)) =
          M + c.bootCount := by omega
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have h1mod : (1 : Nat) % M = 1 := by decide
  simp [selectorBlock, Cfg.coreBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rPi, rP, rJ, rR, rW, rLimit,
    hlt, hKMod, hdiffMod, hsubRaw, h1mod]

end LeanCompCert.Ports.ArraySegMobiusMark

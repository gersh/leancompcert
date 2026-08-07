import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Initial terminal guard for the segmented Möbius prime table

The marking cursor deliberately loads the table entry at its selected limit
before installing the out-of-window terminal offset.  This file isolates the
last five instructions of the production initializer and proves that entry is
the positive configured sentinel.  The schedule induction can therefore keep
division-by-zero behavior out of its invariant.
-/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve

/-- Bootstrap-prime literal stores preceding the fixed terminal guard. -/
def bootInit (c : Cfg) : List AInstr :=
  c.bootTable.zipIdx.flatMap fun (v, t) =>
    [ AInstr.scalar (.mov 90 (.lit (c.primeBase + t)))
    , AInstr.scalar (.mov 91 (.lit v))
    , AInstr.store 90 91 ]

/-- The fixed tail of `Cfg.coreInit`. -/
def initTail (c : Cfg) : List AInstr :=
  [ .scalar (.mov 90 (.lit (c.primeBase + c.tableLen)))
  , .scalar (.mov 91 (.lit c.sentinel))
  , .store 90 91
  , .scalar (.mov rW (.lit 1))
  , .scalar (.mov rWrite (.lit (c.primeBase + c.bootCount))) ]

theorem coreInit_eq_boot_tail (c : Cfg) :
    c.coreInit = bootInit c ++ initTail c := by
  rfl

/-- The production initializer writes a positive guard at the exact selected
main-table limit and opens both persistent cursors at their intended values. -/
theorem arun_coreInit_terminal_guard (c : Cfg) (idx : Nat) (s : AState)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (hA : c.arrayLen < M) :
    let out := arun idx s c.coreInit
    out.arr (c.primeBase + c.tableLen) = c.sentinel ∧
      out.regs rW = 1 ∧
      out.regs rWrite = c.primeBase + c.bootCount := by
  let q := arun idx s (bootInit c)
  have hendM : c.primeBase + c.tableLen < M := by
    simp only [Cfg.primeBase, Cfg.arrayLen, Cfg.resultBase,
      Cfg.tableLen] at hA ⊢
    omega
  have hsentM : c.sentinel < M := by
    simp only [Cfg.sentinel, Cfg.arrayLen, Cfg.resultBase] at hA ⊢
    omega
  have hwriteM : c.primeBase + c.bootCount < M := by
    omega
  have hendMod : (c.primeBase + c.tableLen) % M =
      c.primeBase + c.tableLen := Nat.mod_eq_of_lt hendM
  have hsentMod : c.sentinel % M = c.sentinel :=
    Nat.mod_eq_of_lt hsentM
  have hwriteMod : (c.primeBase + c.bootCount) % M =
      c.primeBase + c.bootCount := Nat.mod_eq_of_lt hwriteM
  have honeMod : (1 : Nat) % M = 1 := by decide
  rw [coreInit_eq_boot_tail, arun_append]
  simp [initTail, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval,
    denoteOperand, AState.writeReg, AState.writeArr_arr_self,
    hendMod, hsentMod, hwriteMod, honeMod, rW, rWrite]

theorem coreInit_terminal_guard_pos (c : Cfg) : 0 < c.sentinel := by
  simp [Cfg.sentinel]

end LeanCompCert.Ports.ArraySegMobiusMark

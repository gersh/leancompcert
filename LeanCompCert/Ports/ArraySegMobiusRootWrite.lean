import LeanCompCert.Ports.ArraySegMobiusRootCompose

/-! # Exact root prime-table write -/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- The production suffix beginning at the root collection gate. -/
def rootWriteSuffix (c : Cfg) : List AInstr :=
  postBeforeRootStore c ++ [.store 141 65] ++ postAfterRootStore c

/-- Separate the write-cursor increment from the remaining window update. -/
def postWriteCursor : List AInstr :=
  [.scalar (.binop rWrite .add (.reg rWrite) (.reg 137))]

def postWindowCursor (c : Cfg) : List AInstr := (postAfterRootStore c).drop 1

theorem postAfterRootStore_eq_cursorSlices (c : Cfg) :
    postAfterRootStore c = postWriteCursor ++ postWindowCursor c := by
  rfl

/-- The final scalar suffix increments the live table cursor exactly once
when collection is enabled. -/
theorem postAfterRootStore_write_collect (c : Cfg) (idx : Nat) (s : AState)
    (write : Nat)
    (hWrite : s.regs rWrite = write)
    (h137 : s.regs 137 = 1)
    (hnextM : write + 1 < M) :
    (arun idx s (postAfterRootStore c)).regs rWrite = write + 1 := by
  let q := arun idx s postWriteCursor
  have hWrite' : s.regs 129 = write := by simpa [rWrite] using hWrite
  have hnextMod : (write + 1) % M = write + 1 := Nat.mod_eq_of_lt hnextM
  have hq : q.regs rWrite = write + 1 := by
    simp [q, postWriteCursor, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rWrite, hWrite', h137, hnextMod]
  rw [postAfterRootStore_eq_cursorSlices, arun_append]
  rw [arun_reg_frame idx rWrite (postWindowCursor c) q (by rfl)]
  exact hq

/-- A collectable root candidate is written to the current live table cell,
and the table cursor advances by one. -/
theorem arun_rootWriteSuffix_collect (c : Cfg) (idx : Nat) (s : AState)
    (n write sink : Nat)
    (h65 : s.regs 65 = n)
    (h67 : s.regs 67 = 1)
    (h132 : s.regs 132 = 1)
    (hWrite : s.regs rWrite = write)
    (hSink : c.primeSink = sink)
    (hn2 : 2 ≤ n)
    (hnCap : n ≤ c.rootCap)
    (hnM : n < M)
    (hcapM : c.rootCap < M)
    (hsinkM : sink < M)
    (hnextM : write + 1 < M) :
    let out := arun idx s (rootWriteSuffix c)
    out.arr write = n ∧ out.regs rWrite = write + 1 := by
  let q := arun idx s (postBeforeRootStore c)
  let t := astep idx q (.store 141 65)
  have hq := postBeforeRootStore_collect_address c idx s n write sink
    h65 h67 h132 hWrite hSink hn2 hnCap hnM hcapM hsinkM (by omega)
  have hq141 : q.regs 141 = write := hq.2.1
  have hq65 : q.regs 65 = n := hq.2.2
  have hq137 : q.regs 137 = 1 := hq.1
  have hqWrite : q.regs rWrite = write := by
    rw [arun_reg_frame idx rWrite (postBeforeRootStore c) s (by rfl)]
    exact hWrite
  have htarr : t.arr write = n := by
    change (q.writeArr (q.regs 141) (q.regs 65)).arr write = n
    rw [hq141, AState.writeArr_arr_self, hq65]
  have htWrite : t.regs rWrite = write := hqWrite
  have ht137 : t.regs 137 = 1 := hq137
  rw [rootWriteSuffix, arun_append, arun_append]
  exact ⟨by
    change (arun idx t (postAfterRootStore c)).arr write = n
    rw [congrFun (arun_arr_frame idx (postAfterRootStore c) t (by rfl)) write]
    exact htarr,
    by
      change (arun idx t (postAfterRootStore c)).regs rWrite = write + 1
      exact postAfterRootStore_write_collect c idx t write htWrite ht137 hnextM⟩

end LeanCompCert.Ports.ArraySegMobiusMark

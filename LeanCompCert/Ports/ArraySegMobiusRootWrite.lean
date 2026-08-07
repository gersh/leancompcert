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

/-- When collection is disabled, the same scalar suffix leaves the table
write cursor unchanged. -/
theorem postAfterRootStore_write_disabled (c : Cfg) (idx : Nat) (s : AState)
    (write : Nat)
    (hWrite : s.regs rWrite = write)
    (h137 : s.regs 137 = 0)
    (hwriteM : write < M) :
    (arun idx s (postAfterRootStore c)).regs rWrite = write := by
  let q := arun idx s postWriteCursor
  have hWrite' : s.regs 129 = write := by simpa [rWrite] using hWrite
  have hwriteMod : write % M = write := Nat.mod_eq_of_lt hwriteM
  have hq : q.regs rWrite = write := by
    simp [q, postWriteCursor, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval,
      denoteOperand, denoteOp, AState.writeReg,
      rWrite, hWrite', h137, hwriteMod]
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

/-- Apart from the selected live table cell, the collection suffix preserves
the entire array.  This is the framing half needed to lift the single verified
store to a represented list append. -/
theorem arun_rootWriteSuffix_collect_frame (c : Cfg) (idx : Nat) (s : AState)
    (n write sink x : Nat)
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
    (hnextM : write + 1 < M)
    (hx : x ≠ write) :
    (arun idx s (rootWriteSuffix c)).arr x = s.arr x := by
  let q := arun idx s (postBeforeRootStore c)
  let t := astep idx q (.store 141 65)
  have hq := postBeforeRootStore_collect_address c idx s n write sink
    h65 h67 h132 hWrite hSink hn2 hnCap hnM hcapM hsinkM (by omega)
  have hq141 : q.regs 141 = write := hq.2.1
  have hqarr : q.arr = s.arr :=
    arun_arr_frame idx (postBeforeRootStore c) s (by rfl)
  rw [rootWriteSuffix, arun_append, arun_append]
  change (arun idx t (postAfterRootStore c)).arr x = s.arr x
  rw [congrFun (arun_arr_frame idx (postAfterRootStore c) t (by rfl)) x]
  change (q.writeArr (q.regs 141) (q.regs 65)).arr x = s.arr x
  rw [hq141, AState.writeArr_arr_ne q _ hx, congrFun hqarr x]

/-- A marked root candidate is redirected to the scratch sink, so every
non-sink array cell and the live table cursor are preserved. -/
theorem arun_rootWriteSuffix_marked_preserves (c : Cfg) (idx : Nat)
    (s : AState) (write x : Nat)
    (h67 : s.regs 67 = 0)
    (hWrite : s.regs rWrite = write)
    (hwriteM : write < M)
    (hA : c.arrayLen < M)
    (hx : x ≠ c.primeSink) :
    let out := arun idx s (rootWriteSuffix c)
    out.arr x = s.arr x ∧ out.regs rWrite = write := by
  let g := arun idx s (postRootGate c)
  let q := arun idx g (postRootAddress c)
  let t := astep idx q (.store 141 65)
  have hg137 : g.regs 137 = 0 := postRootGate_marked c idx s h67
  have hgWrite : g.regs rWrite = write := by
    rw [arun_reg_frame idx rWrite (postRootGate c) s (by rfl)]
    exact hWrite
  have hgarr : g.arr = s.arr :=
    arun_arr_frame idx (postRootGate c) s (by rfl)
  have hq141 : q.regs 141 = c.primeSink :=
    postRootAddress_mark c idx g hg137 hA
  have hq137 : q.regs 137 = 0 := by
    rw [arun_reg_frame idx 137 (postRootAddress c) g (by rfl)]
    exact hg137
  have hqWrite : q.regs rWrite = write := by
    rw [arun_reg_frame idx rWrite (postRootAddress c) g (by rfl)]
    exact hgWrite
  have hqarr : q.arr = s.arr := by
    rw [arun_arr_frame idx (postRootAddress c) g (by rfl)]
    exact hgarr
  have ht137 : t.regs 137 = 0 := hq137
  have htWrite : t.regs rWrite = write := hqWrite
  rw [rootWriteSuffix, postBeforeRootStore_eq_slices, arun_append,
    arun_append, arun_append]
  exact ⟨by
    change (arun idx t (postAfterRootStore c)).arr x = s.arr x
    rw [congrFun (arun_arr_frame idx (postAfterRootStore c) t (by rfl)) x]
    change (q.writeArr (q.regs 141) (q.regs 65)).arr x = s.arr x
    rw [hq141, AState.writeArr_arr_ne q _ hx, congrFun hqarr x],
    by
      change (arun idx t (postAfterRootStore c)).regs rWrite = write
      exact postAfterRootStore_write_disabled c idx t write htWrite ht137
        hwriteM⟩

end LeanCompCert.Ports.ArraySegMobiusMark

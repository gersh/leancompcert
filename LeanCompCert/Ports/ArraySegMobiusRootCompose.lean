import LeanCompCert.Ports.ArraySegMobiusRootAddress

/-! # Composed root prime-table selector -/

namespace LeanCompCert.Ports.ArraySegMobiusMark

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal

/-- The complete eight-instruction root selector routes a collectable
candidate to the live table cursor. -/
theorem postBeforeRootStore_collect_address (c : Cfg) (idx : Nat)
    (s : AState) (n write sink : Nat)
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
    (hwriteM : write < M) :
    let q := arun idx s (postBeforeRootStore c)
    q.regs 137 = 1 ∧ q.regs 141 = write ∧ q.regs 65 = n := by
  let q := arun idx s (postRootGate c)
  have hq137 : q.regs 137 = 1 :=
    postRootGate_collect c idx s n h65 h67 h132 hn2 hnCap hnM hcapM
  have hqWrite : q.regs rWrite = write := by
    rw [arun_reg_frame idx rWrite (postRootGate c) s (by rfl)]
    exact hWrite
  have hq65 : q.regs 65 = n := by
    rw [arun_reg_frame idx 65 (postRootGate c) s (by rfl)]
    exact h65
  rw [postBeforeRootStore_eq_slices, arun_append]
  exact ⟨by
    rw [arun_reg_frame idx 137 (postRootAddress c) q (by rfl)]
    exact hq137,
    postRootAddress_collect c idx q write sink hq137 hqWrite hSink hsinkM
      hwriteM,
    by
      rw [arun_reg_frame idx 65 (postRootAddress c) q (by rfl)]
      exact hq65⟩

end LeanCompCert.Ports.ArraySegMobiusMark

import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceInvariant
import LeanCompCert.Verified.ArrayRegFrame

/-! First historical body cut: exact loading of one reference record. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalLoad (c : Cfg) : List AInstr := c.bodyBlock.take 26

structure HistoricalLoaded (c : Cfg) (words : List Nat) (idx : Nat)
    (before after : AState) : Prop where
  ref_state : refStateOf after = refStateOf before
  array_eq : HistoricalArrayMatches c words after
  tag_eq : after.regs 21 = words.getD (recW * idx) 0
  blk_eq : after.regs 22 = words.getD (recW * idx + 1) 0
  lower_eq : after.regs 23 = words.getD (recW * idx + 2) 0
  slots_eq : after.regs 24 = words.getD (recW * idx + 3) 0
  upper_eq : after.regs 25 = words.getD (recW * idx + 4) 0
  bits_eq : after.regs 26 = words.getD (recW * idx + 5) 0
  stat_eq : after.regs 27 = words.getD (recW * idx + 6) 0
  isLast_eq : after.regs 28 = words.getD (recW * idx + 7) 0
  uElem_eq : after.regs 29 = words.getD (recW * idx + 8) 0
  henc_eq : after.regs 30 = words.getD (recW * idx + 9) 0
  tqNum_eq : after.regs 31 = words.getD (recW * idx + 10) 0
  conjFirst_eq : after.regs 32 = words.getD (recW * idx + 11) 0
  digest_eq : after.regs 158 = words.getD (recW * idx + 12) 0

private theorem historicalLoad_frame (c : Cfg) (idx r : Nat) (s : AState)
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r (historicalLoad c) = false) :
    (arun idx s (historicalLoad c)).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r (historicalLoad c) h s

private def storeFree : AInstr → Bool
  | .store _ _ => false
  | _ => true

private theorem arun_arr_frame (idx : Nat) : ∀ (l : List AInstr) (s : AState),
    l.all storeFree = true → (arun idx s l).arr = s.arr := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr => exact AState.writeReg_arr _ _ _
      | load d a => exact AState.writeReg_arr _ _ _
      | store a v => simp [storeFree] at h

private theorem historicalLoad_arr (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalLoad c)).arr = s.arr :=
  arun_arr_frame idx (historicalLoad c) s (by rfl)

set_option maxRecDepth 10000 in
theorem historicalLoad_loaded
    (c : Cfg) (words : List Nat) (idx : Nat) (s : AState)
    (harray : HistoricalArrayMatches c words s)
    (hstatic : StaticBounds c) (hidx : idx < c.records) :
    HistoricalLoaded c words idx s (arun idx s (historicalLoad c)) := by
  have hbase : 13 * c.records = c.tblBase := rfl
  have hlen : 13 * c.records + 256 < M := by
    simpa [Cfg.arrayLen, recW] using hstatic.array_word
  have cell (off : Nat) (hoff : off ≤ 12) :
      s.arr (13 * idx + off) = words.getD (13 * idx + off) 0 := by
    apply harray.record_cells
    simp only [Cfg.tblBase, recW]
    omega
  have addrMod (off : Nat) (hoff : off ≤ 12) :
      (idx * 13 + off) % M = idx * 13 + off := by
    apply Nat.mod_eq_of_lt
    omega
  have addr0 : (idx * 13) % M = idx * 13 := by
    apply Nat.mod_eq_of_lt
    omega
  refine {
    ref_state := ?_
    array_eq := ?_
    tag_eq := ?_
    blk_eq := ?_
    lower_eq := ?_
    slots_eq := ?_
    upper_eq := ?_
    bits_eq := ?_
    stat_eq := ?_
    isLast_eq := ?_
    uElem_eq := ?_
    henc_eq := ?_
    tqNum_eq := ?_
    conjFirst_eq := ?_
    digest_eq := ?_ }
  · simp only [refStateOf, RefState.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals apply historicalLoad_frame c idx _ s <;> rfl
  · constructor
    · intro k hk
      rw [historicalLoad_arr]
      exact harray.record_cells k hk
    · intro v hv
      rw [historicalLoad_arr]
      exact harray.table_cells v hv
  all_goals
    simp [historicalLoad, Cfg.bodyBlock,
      LeanCompCert.Ports.DirichletLadder.bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, recW, addr0, addrMod 1 (by omega),
      addrMod 2 (by omega), addrMod 3 (by omega), addrMod 4 (by omega),
      addrMod 5 (by omega), addrMod 6 (by omega), addrMod 7 (by omega),
      addrMod 8 (by omega), addrMod 9 (by omega), addrMod 10 (by omega),
      addrMod 11 (by omega), addrMod 12 (by omega)]
    first
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 0 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 1 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 2 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 3 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 4 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 5 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 6 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 7 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 8 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 9 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 10 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 11 (by omega)
    | simpa [Nat.mul_comm, Nat.add_assoc] using cell 12 (by omega)

end LeanCompCert.Ports.DirichletLadderExternalSafety

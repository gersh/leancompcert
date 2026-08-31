import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceByteLoad

/-! Historical instructions 85--99: decode the table-entry low bytes and
sum the eight popcounts.  This file is deliberately a small source cut. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem tblEntry_low_byte (v : Nat) : tblEntry v &&& 255 = popc8 v := by
  rw [show 255 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  have hp : popc8 v < 256 := Nat.lt_of_le_of_lt (popc8_le v) (by decide)
  simp [tblEntry, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hp]

def historicalPopcount (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 85).take 15

set_option maxHeartbeats 1000000 in
theorem historicalPopcount_eq_source (c : Cfg) :
    historicalPopcount c =
      [ bo 69 .band (.reg 54) (.lit 255)
      , bo 70 .band (.reg 56) (.lit 255)
      , bo 71 .band (.reg 58) (.lit 255)
      , bo 72 .band (.reg 60) (.lit 255)
      , bo 73 .band (.reg 62) (.lit 255)
      , bo 74 .band (.reg 64) (.lit 255)
      , bo 75 .band (.reg 66) (.lit 255)
      , bo 76 .band (.reg 68) (.lit 255)
      , bo 77 .add (.reg 69) (.reg 70)
      , bo 77 .add (.reg 77) (.reg 71)
      , bo 77 .add (.reg 77) (.reg 72)
      , bo 77 .add (.reg 77) (.reg 73)
      , bo 77 .add (.reg 77) (.reg 74)
      , bo 77 .add (.reg 77) (.reg 75)
      , bo 77 .add (.reg 77) (.reg 76) ] := by
  rfl

structure HistoricalPopcountLoaded (t : Nat) (s : AState) : Prop where
  byte0 : s.regs 69 = popc8 (byteAt t 0)
  byte1 : s.regs 70 = popc8 (byteAt t 1)
  byte2 : s.regs 71 = popc8 (byteAt t 2)
  byte3 : s.regs 72 = popc8 (byteAt t 3)
  byte4 : s.regs 73 = popc8 (byteAt t 4)
  byte5 : s.regs 74 = popc8 (byteAt t 5)
  byte6 : s.regs 75 = popc8 (byteAt t 6)
  byte7 : s.regs 76 = popc8 (byteAt t 7)

theorem historicalPopcount_loaded
    (c : Cfg) (idx t : Nat) (s : AState)
    (hloaded : HistoricalByteTableLoaded t s) :
    HistoricalPopcountLoaded t (arun idx s (historicalPopcount c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [historicalPopcount_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, hloaded.byte0, hloaded.byte1, hloaded.byte2,
      hloaded.byte3, hloaded.byte4, hloaded.byte5, hloaded.byte6,
      hloaded.byte7]
    simp only [Nat.mod_eq_of_lt (by decide : 255 < M), tblEntry_low_byte]
  all_goals
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (popc8_le _) (by simp [M])

theorem historicalPopcount_result
    (c : Cfg) (idx t : Nat) (s : AState)
    (hloaded : HistoricalByteTableLoaded t s)
    (h63 : (t >>> 63) % 2 = 0) :
    (arun idx s (historicalPopcount c)).regs 77 = bitCount t := by
  have hsum :
      popc8 (byteAt t 0) + popc8 (byteAt t 1) +
        popc8 (byteAt t 2) + popc8 (byteAt t 3) +
        popc8 (byteAt t 4) + popc8 (byteAt t 5) +
        popc8 (byteAt t 6) + popc8 (byteAt t 7) < M := by
    have h0 := popc8_le (byteAt t 0)
    have h1 := popc8_le (byteAt t 1)
    have h2 := popc8_le (byteAt t 2)
    have h3 := popc8_le (byteAt t 3)
    have h4 := popc8_le (byteAt t 4)
    have h5 := popc8_le (byteAt t 5)
    have h6 := popc8_le (byteAt t 6)
    have h7 := popc8_le (byteAt t 7)
    simp only [M]
    omega
  simp [historicalPopcount_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hloaded.byte0, hloaded.byte1, hloaded.byte2,
    hloaded.byte3, hloaded.byte4, hloaded.byte5, hloaded.byte6,
    hloaded.byte7]
  simp only [Nat.mod_eq_of_lt (by decide : 255 < M), tblEntry_low_byte]
  rw [Nat.mod_eq_of_lt hsum]
  exact (bitCount_bytes t h63).symm

theorem historicalPopcount_arr (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalPopcount c)).arr = s.arr := by
  simp [historicalPopcount_eq_source, bo, arun, astep, AState.writeReg_arr]

private theorem popcount_frame (c : Cfg) (idx r : Nat) (s : AState)
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r
      (historicalPopcount c) = false) :
    (arun idx s (historicalPopcount c)).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r
    (historicalPopcount c) h s

theorem historicalPopcount_byteTableLoaded
    (c : Cfg) (idx t : Nat) (s : AState)
    (h : HistoricalByteTableLoaded t s) :
    HistoricalByteTableLoaded t (arun idx s (historicalPopcount c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [popcount_frame c idx _ s (by
      simp [historicalPopcount_eq_source,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        LeanCompCert.Verified.InstrBlock.sdest, bo])]
  · exact h.byte0
  · exact h.byte1
  · exact h.byte2
  · exact h.byte3
  · exact h.byte4
  · exact h.byte5
  · exact h.byte6
  · exact h.byte7

end LeanCompCert.Ports.DirichletLadderExternalSafety

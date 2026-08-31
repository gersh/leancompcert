import LeanCompCert.Ports.DirichletLadderExternalSafetyReferencePopcount

/-! Historical instructions 100--128: reconstruct the bit-position moment
from the eight exact byte-table values. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

theorem tblEntry_high_byte (v : Nat) : tblEntry v >>> 8 = mom8 v := by
  rw [Nat.shiftRight_eq_div_pow]
  change tblEntry v / 256 = mom8 v
  rw [tblEntry, Nat.add_mul_div_left _ _ (by decide : 0 < 256)]
  have hp : popc8 v < 256 := Nat.lt_of_le_of_lt (popc8_le v) (by decide)
  simp [Nat.div_eq_of_lt hp]

def historicalMomentParts (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 100).take 22

set_option maxHeartbeats 1000000 in
theorem historicalMomentParts_eq_source (c : Cfg) :
    historicalMomentParts c =
      [ bo 80 .lshr (.reg 54) (.lit 8)
      , bo 81 .lshr (.reg 56) (.lit 8)
      , bo 82 .mul (.reg 70) (.lit 8)
      , bo 81 .add (.reg 81) (.reg 82)
      , bo 83 .lshr (.reg 58) (.lit 8)
      , bo 84 .mul (.reg 71) (.lit 16)
      , bo 83 .add (.reg 83) (.reg 84)
      , bo 85 .lshr (.reg 60) (.lit 8)
      , bo 86 .mul (.reg 72) (.lit 24)
      , bo 85 .add (.reg 85) (.reg 86)
      , bo 87 .lshr (.reg 62) (.lit 8)
      , bo 88 .mul (.reg 73) (.lit 32)
      , bo 87 .add (.reg 87) (.reg 88)
      , bo 89 .lshr (.reg 64) (.lit 8)
      , bo 90 .mul (.reg 74) (.lit 40)
      , bo 89 .add (.reg 89) (.reg 90)
      , bo 91 .lshr (.reg 66) (.lit 8)
      , bo 92 .mul (.reg 75) (.lit 48)
      , bo 91 .add (.reg 91) (.reg 92)
      , bo 93 .lshr (.reg 68) (.lit 8)
      , bo 94 .mul (.reg 76) (.lit 56)
      , bo 93 .add (.reg 93) (.reg 94) ] := by
  rfl

structure HistoricalMomentPartsLoaded (t : Nat) (s : AState) : Prop where
  byte0 : s.regs 80 = mom8 (byteAt t 0)
  byte1 : s.regs 81 = mom8 (byteAt t 1) + 8 * popc8 (byteAt t 1)
  byte2 : s.regs 83 = mom8 (byteAt t 2) + 16 * popc8 (byteAt t 2)
  byte3 : s.regs 85 = mom8 (byteAt t 3) + 24 * popc8 (byteAt t 3)
  byte4 : s.regs 87 = mom8 (byteAt t 4) + 32 * popc8 (byteAt t 4)
  byte5 : s.regs 89 = mom8 (byteAt t 5) + 40 * popc8 (byteAt t 5)
  byte6 : s.regs 91 = mom8 (byteAt t 6) + 48 * popc8 (byteAt t 6)
  byte7 : s.regs 93 = mom8 (byteAt t 7) + 56 * popc8 (byteAt t 7)

private theorem momentComponent_word (v scale : Nat) (hs : scale ≤ 56) :
    mom8 v + scale * popc8 v < M := by
  have hm := mom8_le v
  have hp := popc8_le v
  have hmul : scale * popc8 v ≤ 56 * 8 := Nat.mul_le_mul hs hp
  simp only [M]
  omega

private theorem momentComponent_le (v scale : Nat) :
    mom8 v + scale * popc8 v ≤ 56 + scale * 8 := by
  exact Nat.add_le_add (mom8_le v) (Nat.mul_le_mul_left scale (popc8_le v))

set_option maxRecDepth 10000 in
theorem historicalMomentParts_loaded
    (c : Cfg) (idx t : Nat) (s : AState)
    (htable : HistoricalByteTableLoaded t s)
    (hpop : HistoricalPopcountLoaded t s) :
    HistoricalMomentPartsLoaded t
      (arun idx s (historicalMomentParts c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [historicalMomentParts_eq_source, bo, arun, astep,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      AState.writeReg, htable.byte0, htable.byte1, htable.byte2,
      htable.byte3, htable.byte4, htable.byte5, htable.byte6, htable.byte7,
      hpop.byte0, hpop.byte1, hpop.byte2, hpop.byte3,
      hpop.byte4, hpop.byte5, hpop.byte6, hpop.byte7,
      ]
  all_goals
    rw [Nat.mod_eq_of_lt (by decide : 8 < M), tblEntry_high_byte]
  · apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt (mom8_le _) (by simp [M])
  · rw [Nat.mul_comm (popc8 (byteAt t 1)) 8]
    rw [Nat.mod_eq_of_lt (momentComponent_word _ 8 (by omega))]
  · rw [Nat.mul_comm (popc8 (byteAt t 2)) 16]
    rw [Nat.mod_eq_of_lt (momentComponent_word _ 16 (by omega))]
  · rw [Nat.mul_comm (popc8 (byteAt t 3)) 24]
    rw [Nat.mod_eq_of_lt (momentComponent_word _ 24 (by omega))]
  · rw [Nat.mul_comm (popc8 (byteAt t 4)) 32]
    rw [Nat.mod_eq_of_lt (momentComponent_word _ 32 (by omega))]
  · rw [Nat.mul_comm (popc8 (byteAt t 5)) 40]
    rw [Nat.mod_eq_of_lt (momentComponent_word _ 40 (by omega))]
  · rw [Nat.mul_comm (popc8 (byteAt t 6)) 48]
    rw [Nat.mod_eq_of_lt (momentComponent_word _ 48 (by omega))]
  · rw [Nat.mul_comm (popc8 (byteAt t 7)) 56]
    rw [Nat.mod_eq_of_lt (momentComponent_word _ 56 (by omega))]

theorem historicalMomentParts_arr (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalMomentParts c)).arr = s.arr := by
  simp [historicalMomentParts_eq_source, bo, arun, astep,
    AState.writeReg_arr]

def historicalMomentSum (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 122).take 7

theorem historicalMomentSum_eq_source (c : Cfg) :
    historicalMomentSum c =
      [ bo 95 .add (.reg 80) (.reg 81)
      , bo 95 .add (.reg 95) (.reg 83)
      , bo 95 .add (.reg 95) (.reg 85)
      , bo 95 .add (.reg 95) (.reg 87)
      , bo 95 .add (.reg 95) (.reg 89)
      , bo 95 .add (.reg 95) (.reg 91)
      , bo 95 .add (.reg 95) (.reg 93) ] := by
  rfl

theorem historicalMomentSum_result
    (c : Cfg) (idx t : Nat) (s : AState)
    (hparts : HistoricalMomentPartsLoaded t s)
    (h63 : (t >>> 63) % 2 = 0) :
    (arun idx s (historicalMomentSum c)).regs 95 = bitMoment t := by
  have h0 := mom8_le (byteAt t 0)
  have h1 := momentComponent_le (byteAt t 1) 8
  have h2 := momentComponent_le (byteAt t 2) 16
  have h3 := momentComponent_le (byteAt t 3) 24
  have h4 := momentComponent_le (byteAt t 4) 32
  have h5 := momentComponent_le (byteAt t 5) 40
  have h6 := momentComponent_le (byteAt t 6) 48
  have h7 := momentComponent_le (byteAt t 7) 56
  have hsum :
      mom8 (byteAt t 0) +
        (mom8 (byteAt t 1) + 8 * popc8 (byteAt t 1)) +
        (mom8 (byteAt t 2) + 16 * popc8 (byteAt t 2)) +
        (mom8 (byteAt t 3) + 24 * popc8 (byteAt t 3)) +
        (mom8 (byteAt t 4) + 32 * popc8 (byteAt t 4)) +
        (mom8 (byteAt t 5) + 40 * popc8 (byteAt t 5)) +
        (mom8 (byteAt t 6) + 48 * popc8 (byteAt t 6)) +
        (mom8 (byteAt t 7) + 56 * popc8 (byteAt t 7)) < M := by
    simp only [M] at *
    omega
  simp [historicalMomentSum_eq_source, bo, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, hparts.byte0, hparts.byte1, hparts.byte2,
    hparts.byte3, hparts.byte4, hparts.byte5, hparts.byte6, hparts.byte7]
  rw [Nat.mod_eq_of_lt hsum]
  exact (bitMoment_bytes t h63).symm

theorem historicalMomentSum_arr (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalMomentSum c)).arr = s.arr := by
  simp [historicalMomentSum_eq_source, bo, arun, astep,
    AState.writeReg_arr]

end LeanCompCert.Ports.DirichletLadderExternalSafety

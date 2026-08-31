import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceTransition

/-! One symbolic byte-table load used by the historical transition counter. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

/-- The uniform four-instruction byte loads for bytes `1` through `7`. -/
def historicalByteLoad (c : Cfg) (b addrReg destReg : Nat) : List AInstr :=
  [ .scalar (.binop addrReg .lshr (.reg 52) (.lit (8 * b)))
  , .scalar (.binop addrReg .band (.reg addrReg) (.lit 255))
  , .scalar (.binop addrReg .add (.reg addrReg) (.lit c.tblBase))
  , .load destReg addrReg ]

def historicalByteLoad0 (c : Cfg) : List AInstr :=
  [ .scalar (.binop 53 .band (.reg 52) (.lit 255))
  , .scalar (.binop 53 .add (.reg 53) (.lit c.tblBase))
  , .load 54 53 ]

theorem historicalByteLoad0_eq (c : Cfg) :
    (c.bodyBlock.drop 54).take 3 = historicalByteLoad0 c := by rfl

theorem historicalByteLoad1_eq (c : Cfg) :
    (c.bodyBlock.drop 57).take 4 = historicalByteLoad c 1 55 56 := by rfl

theorem historicalByteLoad2_eq (c : Cfg) :
    (c.bodyBlock.drop 61).take 4 = historicalByteLoad c 2 57 58 := by rfl

theorem historicalByteLoad3_eq (c : Cfg) :
    (c.bodyBlock.drop 65).take 4 = historicalByteLoad c 3 59 60 := by rfl

theorem historicalByteLoad4_eq (c : Cfg) :
    (c.bodyBlock.drop 69).take 4 = historicalByteLoad c 4 61 62 := by rfl

theorem historicalByteLoad5_eq (c : Cfg) :
    (c.bodyBlock.drop 73).take 4 = historicalByteLoad c 5 63 64 := by rfl

theorem historicalByteLoad6_eq (c : Cfg) :
    (c.bodyBlock.drop 77).take 4 = historicalByteLoad c 6 65 66 := by rfl

theorem historicalByteLoad7_eq (c : Cfg) :
    (c.bodyBlock.drop 81).take 4 = historicalByteLoad c 7 67 68 := by rfl

private theorem and_lt_M {a b : Nat} (ha : a < M) (hb : b < M) :
    a &&& b < M :=
  Nat.bitwise_lt_two_pow (n := 64) ha hb

theorem historicalByteLoad0_result
    (c : Cfg) (words : List Nat) (idx t : Nat) (s : AState)
    (ht : s.regs 52 = t)
    (harray : HistoricalArrayMatches c words s)
    (hstatic : StaticBounds c) :
    (arun idx s (historicalByteLoad0 c)).regs 54 = tblEntry (byteAt t 0) := by
  have h255 : 255 < M := by decide
  have hbyte : byteAt t 0 < 256 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
  have hbyteWord : byteAt t 0 < M := by omega
  have haddrWord : byteAt t 0 + c.tblBase < M := by
    have ha : c.tblBase + 256 < M := by
      simpa [Cfg.arrayLen, Cfg.tblBase] using hstatic.array_word
    omega
  have hcell := harray.table_cells (byteAt t 0) hbyte
  have haddrWord' : (t &&& 255) + c.tblBase < M := by
    simpa [byteAt] using haddrWord
  simp [historicalByteLoad0, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, ht, byteAt, Nat.mod_eq_of_lt h255,
    Nat.mod_eq_of_lt hbyteWord]
  rw [Nat.mod_eq_of_lt haddrWord']
  simpa [byteAt, Nat.add_comm] using hcell

theorem historicalByteLoad_result
    (c : Cfg) (words : List Nat) (idx b addrReg destReg t : Nat) (s : AState)
    (hb : b < 8)
    (ht : s.regs 52 = t) (htWord : t < M)
    (harray : HistoricalArrayMatches c words s)
    (hstatic : StaticBounds c) :
    (arun idx s (historicalByteLoad c b addrReg destReg)).regs destReg =
      tblEntry (byteAt t b) := by
  have hshiftLit : 8 * b < M := by
    have h64 : 64 < M := by decide
    omega
  have hshift : t >>> (8 * b) < M := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) htWord
  have h255 : 255 < M := by decide
  have hbyte : byteAt t b < 256 := by
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
  have hbyteWord : byteAt t b < M := by omega
  have haddrWord : byteAt t b + c.tblBase < M := by
    have ha : c.tblBase + 256 < M := by
      simpa [Cfg.arrayLen, Cfg.tblBase] using hstatic.array_word
    omega
  have hcell := harray.table_cells (byteAt t b) hbyte
  have haddrWord' : (t >>> (8 * b) &&& 255) + c.tblBase < M := by
    simpa [byteAt] using haddrWord
  simp [historicalByteLoad, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, ht, byteAt,
    Nat.mod_eq_of_lt hshiftLit, Nat.mod_eq_of_lt hshift,
    Nat.mod_eq_of_lt h255, Nat.mod_eq_of_lt hbyteWord,
    Nat.add_comm]
  rw [Nat.mod_eq_of_lt haddrWord']
  simpa [byteAt, Nat.add_comm] using hcell

theorem historicalByteLoad_arr
    (c : Cfg) (idx b addrReg destReg : Nat) (s : AState) :
    (arun idx s (historicalByteLoad c b addrReg destReg)).arr = s.arr := by
  simp [historicalByteLoad, arun, astep, AState.writeReg_arr]

theorem historicalByteLoad0_arr (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalByteLoad0 c)).arr = s.arr := by
  simp [historicalByteLoad0, arun, astep, AState.writeReg_arr]

theorem historicalByteLoad_arrayMatches
    (c : Cfg) (words : List Nat) (idx b addrReg destReg : Nat) (s : AState)
    (h : HistoricalArrayMatches c words s) :
    HistoricalArrayMatches c words
      (arun idx s (historicalByteLoad c b addrReg destReg)) := by
  constructor
  · intro k hk
    rw [historicalByteLoad_arr]
    exact h.record_cells k hk
  · intro v hv
    rw [historicalByteLoad_arr]
    exact h.table_cells v hv

theorem historicalByteLoad0_arrayMatches
    (c : Cfg) (words : List Nat) (idx : Nat) (s : AState)
    (h : HistoricalArrayMatches c words s) :
    HistoricalArrayMatches c words (arun idx s (historicalByteLoad0 c)) := by
  constructor
  · intro k hk
    rw [historicalByteLoad0_arr]
    exact h.record_cells k hk
  · intro v hv
    rw [historicalByteLoad0_arr]
    exact h.table_cells v hv

structure HistoricalByteTableLoaded (t : Nat) (s : AState) : Prop where
  byte0 : s.regs 54 = tblEntry (byteAt t 0)
  byte1 : s.regs 56 = tblEntry (byteAt t 1)
  byte2 : s.regs 58 = tblEntry (byteAt t 2)
  byte3 : s.regs 60 = tblEntry (byteAt t 3)
  byte4 : s.regs 62 = tblEntry (byteAt t 4)
  byte5 : s.regs 64 = tblEntry (byteAt t 5)
  byte6 : s.regs 66 = tblEntry (byteAt t 6)
  byte7 : s.regs 68 = tblEntry (byteAt t 7)

def historicalByteLoads (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 54).take 31

theorem historicalByteLoads_eq_parts (c : Cfg) :
    historicalByteLoads c = historicalByteLoad0 c ++
      historicalByteLoad c 1 55 56 ++ historicalByteLoad c 2 57 58 ++
      historicalByteLoad c 3 59 60 ++ historicalByteLoad c 4 61 62 ++
      historicalByteLoad c 5 63 64 ++ historicalByteLoad c 6 65 66 ++
      historicalByteLoad c 7 67 68 := by
  rfl

private theorem frame {idx r : Nat} {s : AState} {l : List AInstr}
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

set_option maxRecDepth 10000 in
theorem historicalByteLoads_result
    (c : Cfg) (words : List Nat) (idx t : Nat) (s : AState)
    (ht : s.regs 52 = t) (htWord : t < M)
    (harray : HistoricalArrayMatches c words s)
    (hstatic : StaticBounds c) :
    let out := arun idx s (historicalByteLoads c)
    HistoricalByteTableLoaded t out ∧ HistoricalArrayMatches c words out := by
  let s0 := arun idx s (historicalByteLoad0 c)
  let s1 := arun idx s0 (historicalByteLoad c 1 55 56)
  let s2 := arun idx s1 (historicalByteLoad c 2 57 58)
  let s3 := arun idx s2 (historicalByteLoad c 3 59 60)
  let s4 := arun idx s3 (historicalByteLoad c 4 61 62)
  let s5 := arun idx s4 (historicalByteLoad c 5 63 64)
  let s6 := arun idx s5 (historicalByteLoad c 6 65 66)
  let s7 := arun idx s6 (historicalByteLoad c 7 67 68)
  have ht0 : s0.regs 52 = t := by
    rw [frame (idx := idx) (s := s) (l := historicalByteLoad0 c) (r := 52) (by rfl)]
    exact ht
  have ha0 := historicalByteLoad0_arrayMatches c words idx s harray
  have h0 := historicalByteLoad0_result c words idx t s ht harray hstatic
  have ht1 : s1.regs 52 = t := by
    rw [frame (idx := idx) (s := s0) (l := historicalByteLoad c 1 55 56)
      (r := 52) (by rfl)]
    exact ht0
  have ha1 := historicalByteLoad_arrayMatches c words idx 1 55 56 s0 ha0
  have h1 := historicalByteLoad_result c words idx 1 55 56 t s0 (by omega)
    ht0 htWord ha0 hstatic
  have ht2 : s2.regs 52 = t := by
    rw [frame (idx := idx) (s := s1) (l := historicalByteLoad c 2 57 58)
      (r := 52) (by rfl)]
    exact ht1
  have ha2 := historicalByteLoad_arrayMatches c words idx 2 57 58 s1 ha1
  have h2 := historicalByteLoad_result c words idx 2 57 58 t s1 (by omega)
    ht1 htWord ha1 hstatic
  have ht3 : s3.regs 52 = t := by
    rw [frame (idx := idx) (s := s2) (l := historicalByteLoad c 3 59 60)
      (r := 52) (by rfl)]
    exact ht2
  have ha3 := historicalByteLoad_arrayMatches c words idx 3 59 60 s2 ha2
  have h3 := historicalByteLoad_result c words idx 3 59 60 t s2 (by omega)
    ht2 htWord ha2 hstatic
  have ht4 : s4.regs 52 = t := by
    rw [frame (idx := idx) (s := s3) (l := historicalByteLoad c 4 61 62)
      (r := 52) (by rfl)]
    exact ht3
  have ha4 := historicalByteLoad_arrayMatches c words idx 4 61 62 s3 ha3
  have h4 := historicalByteLoad_result c words idx 4 61 62 t s3 (by omega)
    ht3 htWord ha3 hstatic
  have ht5 : s5.regs 52 = t := by
    rw [frame (idx := idx) (s := s4) (l := historicalByteLoad c 5 63 64)
      (r := 52) (by rfl)]
    exact ht4
  have ha5 := historicalByteLoad_arrayMatches c words idx 5 63 64 s4 ha4
  have h5 := historicalByteLoad_result c words idx 5 63 64 t s4 (by omega)
    ht4 htWord ha4 hstatic
  have ht6 : s6.regs 52 = t := by
    rw [frame (idx := idx) (s := s5) (l := historicalByteLoad c 6 65 66)
      (r := 52) (by rfl)]
    exact ht5
  have ha6 := historicalByteLoad_arrayMatches c words idx 6 65 66 s5 ha5
  have h6 := historicalByteLoad_result c words idx 6 65 66 t s5 (by omega)
    ht5 htWord ha5 hstatic
  have ht7 : s7.regs 52 = t := by
    rw [frame (idx := idx) (s := s6) (l := historicalByteLoad c 7 67 68)
      (r := 52) (by rfl)]
    exact ht6
  have ha7 := historicalByteLoad_arrayMatches c words idx 7 67 68 s6 ha6
  have h7 := historicalByteLoad_result c words idx 7 67 68 t s6 (by omega)
    ht6 htWord ha6 hstatic
  rw [historicalByteLoads_eq_parts, arun_append, arun_append, arun_append,
    arun_append, arun_append, arun_append, arun_append]
  change HistoricalByteTableLoaded t s7 ∧ HistoricalArrayMatches c words s7
  refine ⟨?_, ha7⟩
  refine {
    byte0 := ?_, byte1 := ?_, byte2 := ?_, byte3 := ?_,
    byte4 := ?_, byte5 := ?_, byte6 := ?_, byte7 := h7 }
  · rw [frame (idx := idx) (s := s6) (l := historicalByteLoad c 7 67 68) (r := 54) (by rfl),
      frame (idx := idx) (s := s5) (l := historicalByteLoad c 6 65 66) (r := 54) (by rfl),
      frame (idx := idx) (s := s4) (l := historicalByteLoad c 5 63 64) (r := 54) (by rfl),
      frame (idx := idx) (s := s3) (l := historicalByteLoad c 4 61 62) (r := 54) (by rfl),
      frame (idx := idx) (s := s2) (l := historicalByteLoad c 3 59 60) (r := 54) (by rfl),
      frame (idx := idx) (s := s1) (l := historicalByteLoad c 2 57 58) (r := 54) (by rfl),
      frame (idx := idx) (s := s0) (l := historicalByteLoad c 1 55 56) (r := 54) (by rfl)]
    exact h0
  · rw [frame (idx := idx) (s := s6) (l := historicalByteLoad c 7 67 68) (r := 56) (by rfl),
      frame (idx := idx) (s := s5) (l := historicalByteLoad c 6 65 66) (r := 56) (by rfl),
      frame (idx := idx) (s := s4) (l := historicalByteLoad c 5 63 64) (r := 56) (by rfl),
      frame (idx := idx) (s := s3) (l := historicalByteLoad c 4 61 62) (r := 56) (by rfl),
      frame (idx := idx) (s := s2) (l := historicalByteLoad c 3 59 60) (r := 56) (by rfl),
      frame (idx := idx) (s := s1) (l := historicalByteLoad c 2 57 58) (r := 56) (by rfl)]
    exact h1
  · rw [frame (idx := idx) (s := s6) (l := historicalByteLoad c 7 67 68) (r := 58) (by rfl),
      frame (idx := idx) (s := s5) (l := historicalByteLoad c 6 65 66) (r := 58) (by rfl),
      frame (idx := idx) (s := s4) (l := historicalByteLoad c 5 63 64) (r := 58) (by rfl),
      frame (idx := idx) (s := s3) (l := historicalByteLoad c 4 61 62) (r := 58) (by rfl),
      frame (idx := idx) (s := s2) (l := historicalByteLoad c 3 59 60) (r := 58) (by rfl)]
    exact h2
  · rw [frame (idx := idx) (s := s6) (l := historicalByteLoad c 7 67 68) (r := 60) (by rfl),
      frame (idx := idx) (s := s5) (l := historicalByteLoad c 6 65 66) (r := 60) (by rfl),
      frame (idx := idx) (s := s4) (l := historicalByteLoad c 5 63 64) (r := 60) (by rfl),
      frame (idx := idx) (s := s3) (l := historicalByteLoad c 4 61 62) (r := 60) (by rfl)]
    exact h3
  · rw [frame (idx := idx) (s := s6) (l := historicalByteLoad c 7 67 68) (r := 62) (by rfl),
      frame (idx := idx) (s := s5) (l := historicalByteLoad c 6 65 66) (r := 62) (by rfl),
      frame (idx := idx) (s := s4) (l := historicalByteLoad c 5 63 64) (r := 62) (by rfl)]
    exact h4
  · rw [frame (idx := idx) (s := s6) (l := historicalByteLoad c 7 67 68) (r := 64) (by rfl),
      frame (idx := idx) (s := s5) (l := historicalByteLoad c 6 65 66) (r := 64) (by rfl)]
    exact h5
  · rw [frame (idx := idx) (s := s6) (l := historicalByteLoad c 7 67 68) (r := 66) (by rfl)]
    exact h6

end LeanCompCert.Ports.DirichletLadderExternalSafety

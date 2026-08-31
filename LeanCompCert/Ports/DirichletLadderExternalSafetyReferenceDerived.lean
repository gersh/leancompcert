import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceMoment

/-! Compose historical instructions 51--128 without unfolding the full body. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalDerived (c : Cfg) : List AInstr :=
  (c.bodyBlock.drop 51).take 78

theorem historicalDerived_eq_parts (c : Cfg) :
    historicalDerived c = historicalTransitionWord c ++
      historicalByteLoads c ++ historicalPopcount c ++
      historicalMomentParts c ++ historicalMomentSum c := by
  rfl

structure HistoricalDerivedLoaded (bits : Nat) (s : AState) : Prop where
  trI : s.regs 77 = bitCount (transWord bits)
  sj : s.regs 95 = bitMoment (transWord bits)

private theorem scalarBlock_frame (idx r : Nat) (s : AState)
    (l : List AInstr)
    (h : LeanCompCert.Verified.ArrayRegFrame.writes r l = false) :
    (arun idx s l).regs r = s.regs r :=
  LeanCompCert.Verified.ArrayRegFrame.arun_frame idx r l h s

private theorem transition_arr (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalTransitionWord c)).arr = s.arr := by
  simp [historicalTransitionWord_eq, arun, astep, AState.writeReg_arr]

private theorem arrayMatches_of_arr_eq
    (c : Cfg) (words : List Nat) (before after : AState)
    (heq : after.arr = before.arr)
    (h : HistoricalArrayMatches c words before) :
    HistoricalArrayMatches c words after := by
  constructor
  · intro k hk
    rw [heq]
    exact h.record_cells k hk
  · intro v hv
    rw [heq]
    exact h.table_cells v hv

set_option maxRecDepth 10000 in
theorem historicalDerived_result
    (c : Cfg) (words : List Nat) (idx bits : Nat) (s : AState)
    (hbits : s.regs 26 = bits) (hbitsWord : bits < M)
    (harray : HistoricalArrayMatches c words s)
    (hstatic : StaticBounds c) :
    let out := arun idx s (historicalDerived c)
    HistoricalDerivedLoaded bits out ∧
      HistoricalArrayMatches c words out := by
  let t := transWord bits
  let sT := arun idx s (historicalTransitionWord c)
  let sB := arun idx sT (historicalByteLoads c)
  let sP := arun idx sB (historicalPopcount c)
  let sM := arun idx sP (historicalMomentParts c)
  let sS := arun idx sM (historicalMomentSum c)
  have ht : sT.regs 52 = t := by
    exact historicalTransitionWord_result c idx bits s hbits hbitsWord
  have htWord : t < M := by
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide : mask63 < M)
  have haT : HistoricalArrayMatches c words sT :=
    arrayMatches_of_arr_eq c words s sT (transition_arr c idx s) harray
  have hB := historicalByteLoads_result c words idx t sT ht htWord haT hstatic
  have htableB : HistoricalByteTableLoaded t sB := hB.1
  have haB : HistoricalArrayMatches c words sB := hB.2
  have hpop : HistoricalPopcountLoaded t sP :=
    historicalPopcount_loaded c idx t sB htableB
  have htableP : HistoricalByteTableLoaded t sP :=
    historicalPopcount_byteTableLoaded c idx t sB htableB
  have htrI_P : sP.regs 77 = bitCount t :=
    historicalPopcount_result c idx t sB htableB
      (by exact transWord_bit63_zero bits)
  have haP : HistoricalArrayMatches c words sP :=
    arrayMatches_of_arr_eq c words sB sP
      (historicalPopcount_arr c idx sB) haB
  have hparts : HistoricalMomentPartsLoaded t sM :=
    historicalMomentParts_loaded c idx t sP htableP hpop
  have haM : HistoricalArrayMatches c words sM :=
    arrayMatches_of_arr_eq c words sP sM
      (historicalMomentParts_arr c idx sP) haP
  have hsj : sS.regs 95 = bitMoment t :=
    historicalMomentSum_result c idx t sM hparts
      (by exact transWord_bit63_zero bits)
  have htrI_M : sM.regs 77 = bitCount t := by
    rw [scalarBlock_frame idx 77 sP (historicalMomentParts c) (by
      simp [historicalMomentParts_eq_source,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        LeanCompCert.Verified.InstrBlock.sdest, bo])]
    exact htrI_P
  have htrI_S : sS.regs 77 = bitCount t := by
    rw [scalarBlock_frame idx 77 sM (historicalMomentSum c) (by
      simp [historicalMomentSum_eq_source,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites,
        LeanCompCert.Verified.InstrBlock.sdest, bo])]
    exact htrI_M
  have haS : HistoricalArrayMatches c words sS :=
    arrayMatches_of_arr_eq c words sM sS
      (historicalMomentSum_arr c idx sM) haM
  rw [historicalDerived_eq_parts, arun_append, arun_append,
    arun_append, arun_append]
  change HistoricalDerivedLoaded bits sS ∧ HistoricalArrayMatches c words sS
  exact ⟨⟨htrI_S, hsj⟩, haS⟩

end LeanCompCert.Ports.DirichletLadderExternalSafety

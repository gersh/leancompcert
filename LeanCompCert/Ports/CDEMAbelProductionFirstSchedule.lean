import LeanCompCert.Ports.CDEMAbelProductionFirstEntry
import LeanCompCert.Ports.CDEMAbelSourceTelescope

/-! # First active production CDEM scheduler cell -/

namespace LeanCompCert.Ports.CDEMAbelProductionFirstSchedule

open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelAccumulation
open LeanCompCert.Ports.CDEMAbelBisection
open LeanCompCert.Ports.CDEMAbelBody
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelOuterReady
open LeanCompCert.Ports.CDEMAbelSourceReady
open LeanCompCert.Ports.CDEMAbelSourceTelescope
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelMarkTermination
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor
open LeanCompCert.Ports.CDEMAbelProductionSieveState
open LeanCompCert.Ports.CDEMAbelProductionMarkState
open LeanCompCert.Ports.CDEMAbelProductionFirstEntry
open LeanCompCert.Ports.CDEMAbelProductionInactiveMark

/-- The literal instruction index of the first active accumulation cell. -/
def productionFirstIdx : Nat :=
  productionCfg.sieveLen + productionCfg.markSteps

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- A zero signed delta cannot overflow the final wide accumulator, because
the literal body preserves the machine-word invariant of both limbs. -/
theorem zeroDeltaFinalFit (c : Cfg) (idx : Nat) (st : AState) (k : Nat)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M) :
    let current := bodyIter c idx (c.bsSteps - 1) (arun idx st c.body)
    AddWide.wval (current.regs rVLo, current.regs rVHi) +
      (0 + 0) * exactRoot c.wScale k < AddWide.B128 := by
  have hfirstWord := arun_word idx c.body st hword harrword
  have hcurrentWord := bodyIter_word c idx (c.bsSteps - 1)
    (arun idx st c.body)
    hfirstWord.1 hfirstWord.2
  have hwide := wide_lt_of_word
    (bodyIter c idx (c.bsSteps - 1) (arun idx st c.body)).regs
    rVLo rVHi hcurrentWord.1
  simpa only [Nat.zero_add, Nat.zero_mul, Nat.add_zero] using hwide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
/-- The first active production cell satisfies the full bisection and
accumulation contract.  Its signed delta is zero, so the final wide-product
guard follows solely from the invariant that both limbs are machine words. -/
theorem production_first_schedule
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    OuterFullAccSpec productionCfg (nextKey st)
        (nextDPos productionCfg st) (nextDNeg productionCfg st)
        (nextCeil productionCfg st) (nextFloor productionCfg st)
        (exactRoot productionCfg.wScale (nextKey st))
        (nextDPos productionCfg st + nextDNeg productionCfg st)
        st (bodySchedule productionCfg productionFirstIdx
          (productionCfg.bsSteps - 1) st) ∧
      ProductionCellCursorSpec productionCfg (st.regs rC) (st.regs rR)
        (st.regs rW) (bodySchedule productionCfg productionFirstIdx
          (productionCfg.bsSteps - 1) st) := by
  let st := bodyIterFrom productionCfg productionCfg.sieveLen
    productionCfg.markSteps productionAfterSieve
  have hentry0 := productionAfterMark_firstEntry hbudget
  dsimp only at hentry0
  have hentry : FirstEntryInv productionCfg st := hentry0
  rcases productionAfterMark_cursor with ⟨hr0, hw0, hc0, _hz0⟩
  have hr : st.regs rR = productionCfg.markSteps := hr0
  have hw : st.regs rW = 1 := hw0
  have hc : st.regs rC = 0 := hc0
  have hkey : nextKey st = 1 := by rw [nextKey, hw, hc]
  have hdpos : nextDPos productionCfg st = 0 := by
    rcases productionAfterMark_source_seed with
      ⟨hf0, _ht0, _ht20, he0, _htv0, _hk0, _hdp0, _hdn0, _hzero0⟩
    have hf : st.regs rF = 0 := hf0
    have he : st.regs rE = 0 := he0
    have hcell0 := LeanCompCert.Ports.CDEMAbelProductionFirstWindow.productionAfterMark_first_cell hbudget
    dsimp only at hcell0
    have hcell : st.arr productionCfg.winBase = 1 := hcell0
    rw [nextDPos, nextF, hf, hc, he]
    simp only [Nat.zero_add, hcell]
    decide
  have hdneg : nextDNeg productionCfg st = 0 := by
    rcases productionAfterMark_source_seed with
      ⟨hf0, _ht0, _ht20, he0, _htv0, _hk0, _hdp0, _hdn0, _hzero0⟩
    have hf : st.regs rF = 0 := hf0
    have he : st.regs rE = 0 := he0
    have hcell0 := LeanCompCert.Ports.CDEMAbelProductionFirstWindow.productionAfterMark_first_cell hbudget
    dsimp only at hcell0
    have hcell : st.arr productionCfg.winBase = 1 := hcell0
    rw [nextDNeg, nextF, hf, hc, he]
    simp only [Nat.zero_add, hcell]
    decide
  apply bodySchedule_production_of_entry productionCfg productionFirstIdx st
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [hr]
    exact Nat.le_refl _
  · decide
  · decide
  · decide
  · rw [hw]
    decide
  · rw [hr, hc]
    simp only [Nat.zero_mul, Nat.add_zero]
  · exact hentry
  · rw [hkey]
    decide
  · dsimp only
    rw [hdpos, hdneg]
    exact zeroDeltaFinalFit productionCfg productionFirstIdx st
      (nextKey st) hentry.regs_word hentry.arr_word

end LeanCompCert.Ports.CDEMAbelProductionFirstSchedule

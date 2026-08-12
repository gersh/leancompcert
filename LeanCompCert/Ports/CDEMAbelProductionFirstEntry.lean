import LeanCompCert.Ports.CDEMAbelProductionFirstWindow
import LeanCompCert.Ports.CDEMAbelProductionInactiveMark
import LeanCompCert.Ports.CDEMAbelProductionInactiveWide
import LeanCompCert.Ports.CDEMAbelProductionMarkState
import LeanCompCert.Ports.CDEMAbelSourceReady

/-! # First production CDEM accumulation entry -/

namespace LeanCompCert.Ports.CDEMAbelProductionFirstEntry

open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelMarkPlaneBudget
open LeanCompCert.Ports.CDEMAbelMarkTermination
open LeanCompCert.Ports.CDEMAbelAccumulation
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor
open LeanCompCert.Ports.CDEMAbelProductionSieveState
open LeanCompCert.Ports.CDEMAbelProductionFirstWindow
open LeanCompCert.Ports.CDEMAbelProductionInactiveMark
open LeanCompCert.Ports.CDEMAbelProductionInactiveWide
open LeanCompCert.Ports.CDEMAbelProductionMarkState
open LeanCompCert.Ports.CDEMAbelSourceReady

set_option maxRecDepth 4096 in
/-- The finite sieve and marking computations enter the first production
accumulation cell with every source-facing and wide no-wrap invariant needed
by the verified literal scheduler. -/
theorem productionAfterMark_firstEntry
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let out := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    FirstEntryInv productionCfg out := by
  let out := bodyIterFrom productionCfg productionCfg.sieveLen
    productionCfg.markSteps productionAfterSieve
  rcases productionAfterMark_source_seed with
    ⟨hf, ht, ht2, he, htv, _hk, _hdp, _hdn, hzero⟩
  rcases productionAfterMark_wide_seed with
    ⟨hup, hun, _hv, hround⟩
  rcases productionAfterMark_cursor with ⟨_hr, hw, hc, _hzero'⟩
  rcases productionAfterMark_word with ⟨hregs, harr⟩
  have hf' : out.regs rF = 0 := hf
  have ht' : out.regs rT = 1 := ht
  have ht2' : out.regs rT2 = 4 := ht2
  have he' : out.regs rE = 0 := he
  have htv' : out.regs rTv = 0 := htv
  have hzero' : out.regs rZero = 0 := hzero
  have hround' : out.regs rKr = 0 := hround
  have hw' : out.regs rW = 1 := hw
  have hc' : out.regs rC = 0 := hc
  have hup' : AddWide.wval (out.regs rUpLo, out.regs rUpHi) = 0 := hup
  have hun' : AddWide.wval (out.regs rUnLo, out.regs rUnHi) = 0 := hun
  have hregs' : ∀ j, out.regs j < M := hregs
  have harr' : ∀ j, out.arr j < M := harr
  have hcell0 := productionAfterMark_first_cell hbudget
  dsimp only at hcell0
  have hcell : out.arr productionCfg.winBase = 1 := hcell0
  have hkey : nextKey out = 1 := by
    rw [nextKey, hw', hc']
  have hnextF : nextF productionCfg out = 1 := by
    rw [nextF, hf', hc']
    simp only [Nat.zero_add, hcell]
    decide
  have hdpos : nextDPos productionCfg out = 0 := by
    rw [nextDPos, hnextF, he']
    decide
  have hdneg : nextDNeg productionCfg out = 0 := by
    rw [nextDNeg, hnextF, he']
    decide
  refine
    { round0 := hround'
      zero := hzero'
      cell_range := by rw [hc']; decide
      sqrt := ?_
      steps_pos := by decide
      steps_word := by decide
      addr_word := by rw [hc']; decide
      regs_word := hregs'
      arr_word := harr'
      key_pos := by rw [hkey]; decide
      key_word := by rw [hkey]; decide
      t_word := by rw [ht']; decide
      double_word := by rw [ht']; decide
      t2_word := by rw [ht2', ht']; decide
      scale_pos := by decide
      scale_word := by decide
      delta_sum_word := by rw [hdpos, hdneg]; decide
      tv_word := by rw [htv', hdpos, hdneg]; decide
      ceil_word := by rw [hkey]; decide
      scale_plus_sqrt_word := by rw [hkey]; decide
      uPos_fit := by rw [hup', hdpos]; simp [AddWide.B128]
      uNeg_fit := by rw [hun', hdneg]; simp [AddWide.B128] }
  exact
    { nextSquare := by rw [ht2', ht']
      lower := by rw [ht', hw', hc']; decide
      oneBump := by rw [ht', hw', hc']; decide }

set_option maxRecDepth 4096 in
/-- Compact source values consumed by the first active scheduler and the
following interior handoff. -/
theorem productionAfterMark_first_values
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let out := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    nextKey out = 1 ∧ nextF productionCfg out = 1 ∧
      nextDPos productionCfg out = 0 ∧ nextDNeg productionCfg out = 0 := by
  let out := bodyIterFrom productionCfg productionCfg.sieveLen
    productionCfg.markSteps productionAfterSieve
  rcases productionAfterMark_source_seed with
    ⟨hf0, _ht0, _ht20, he0, _htv0, _hk0, _hdp0, _hdn0, _hzero0⟩
  rcases productionAfterMark_cursor with ⟨_hr0, hw0, hc0, _hz0⟩
  have hf : out.regs rF = 0 := hf0
  have he : out.regs rE = 0 := he0
  have hw : out.regs rW = 1 := hw0
  have hc : out.regs rC = 0 := hc0
  have hcell0 := productionAfterMark_first_cell hbudget
  dsimp only at hcell0
  have hcell : out.arr productionCfg.winBase = 1 := hcell0
  have hkey : nextKey out = 1 := by rw [nextKey, hw, hc]
  have hnextF : nextF productionCfg out = 1 := by
    rw [nextF, hf, hc]
    simp only [Nat.zero_add, hcell]
    decide
  exact ⟨hkey, hnextF,
    by rw [nextDPos, hnextF, he]; decide,
    by rw [nextDNeg, hnextF, he]; decide⟩

end LeanCompCert.Ports.CDEMAbelProductionFirstEntry

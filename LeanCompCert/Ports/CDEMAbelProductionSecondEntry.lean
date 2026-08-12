import LeanCompCert.Ports.CDEMAbelProductionFirstSchedule

/-! # Second production CDEM accumulation entry -/

namespace LeanCompCert.Ports.CDEMAbelProductionSecondEntry

open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelAccumulation
open LeanCompCert.Ports.CDEMAbelBisection
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelOuterReady
open LeanCompCert.Ports.CDEMAbelSourceReady
open LeanCompCert.Ports.CDEMAbelSourceTelescope
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelMarkTermination
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor
open LeanCompCert.Ports.CDEMAbelProductionSieveState
open LeanCompCert.Ports.CDEMAbelProductionFirstWindow
open LeanCompCert.Ports.CDEMAbelProductionFirstEntry
open LeanCompCert.Ports.CDEMAbelProductionFirstSchedule
open LeanCompCert.Ports.CDEMAbelProductionInactiveMark
open LeanCompCert.Ports.CDEMAbelProductionInactiveWide
open LeanCompCert.Ports.CDEMAbelProductionMarkState

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Compact structural handoff from the full first scheduler cell. -/
theorem production_first_stream_step
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    InteriorStreamStepSpec productionCfg (nextDPos productionCfg st)
      (nextDNeg productionCfg st) st after := by
  let st := bodyIterFrom productionCfg productionCfg.sieveLen
    productionCfg.markSteps productionAfterSieve
  let after := bodySchedule productionCfg productionFirstIdx
    (productionCfg.bsSteps - 1) st
  have hentry0 := productionAfterMark_firstEntry hbudget
  dsimp only at hentry0
  have hentry : FirstEntryInv productionCfg st := hentry0
  have hschedule0 := production_first_schedule hbudget
  dsimp only at hschedule0
  have hschedule :
      OuterFullAccSpec productionCfg (nextKey st)
          (nextDPos productionCfg st) (nextDNeg productionCfg st)
          (nextCeil productionCfg st) (nextFloor productionCfg st)
          (exactRoot productionCfg.wScale (nextKey st))
          (nextDPos productionCfg st + nextDNeg productionCfg st) st after ∧
        ProductionCellCursorSpec productionCfg (st.regs rC) (st.regs rR)
          (st.regs rW) after := hschedule0
  rcases productionAfterMark_cursor with ⟨_hr0, _hw0, hc0, _hz0⟩
  have hc : st.regs rC = 0 := hc0
  exact interior_stream_step_of_full productionCfg st after
    (nextKey st) (nextDPos productionCfg st) (nextDNeg productionCfg st)
    (nextCeil productionCfg st) (nextFloor productionCfg st)
    (exactRoot productionCfg.wScale (nextKey st))
    (nextDPos productionCfg st + nextDNeg productionCfg st)
    (st.regs rC) (st.regs rR) (st.regs rW) hentry hschedule.1
    hschedule.2 rfl rfl (by rw [hc]; decide)

set_option maxRecDepth 4096 in
/-- Exact square-root cursor after the first active cell. -/
theorem production_second_t
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    after.regs rT = 1 := by
  dsimp only
  have hs := production_first_schedule hbudget
  rcases productionAfterMark_cursor with ⟨_hr, hw, hc, _hz⟩
  rcases productionAfterMark_source_seed with
    ⟨_hf, ht, ht2, _he, _htv, _hk, _hdp, _hdn, _hzero⟩
  rw [hs.1.t, hw, hc, ht2, ht]
  decide

set_option maxRecDepth 4096 in
/-- Exact next-square cursor after the first active cell. -/
theorem production_second_t2
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    after.regs rT2 = 4 := by
  dsimp only
  have hs := production_first_schedule hbudget
  rcases productionAfterMark_cursor with ⟨_hr, hw, hc, _hz⟩
  rcases productionAfterMark_source_seed with
    ⟨_hf, ht, ht2, _he, _htv, _hk, _hdp, _hdn, _hzero⟩
  rw [hs.1.t2, hw, hc, ht2, ht]
  decide

structure SecondSourceValues (after : AState) : Prop where
  key : nextKey after = 2
  t : after.regs rT = 1
  t2 : after.regs rT2 = 4
  nextF : LeanCompCert.Ports.CDEMAbelSourceReady.nextF productionCfg after = 1
  e : after.regs rE = 0
  dPos : nextDPos productionCfg after = 0
  dNeg : nextDNeg productionCfg after = 0
  tv : after.regs rTv = 0

set_option maxRecDepth 4096 in
theorem production_second_key
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    nextKey after = 2 := by
  dsimp only
  have hstream := production_first_stream_step hbudget
  dsimp only at hstream
  rcases productionAfterMark_cursor with ⟨_hr, hw, hc, _hz⟩
  rw [nextKey, hstream.window, hstream.cell, hw, hc]

theorem secondNextF_of_stream (c : Cfg) (before after : AState)
    (dp dn : Nat) (hstream : InteriorStreamStepSpec c dp dn before after)
    (hnextF : nextF c before = 1) (hcell : before.regs rC = 0)
    (hsecond : before.arr (1 + c.winBase) = 0) :
    nextF c after = 1 := by
  rw [hstream.nextF, hnextF, hcell, hsecond]
  decide

set_option maxRecDepth 4096 in
theorem production_second_nextF
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps)
    (hdelta : Ref.deltaF productionCfg.kBound 2 = 0) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    LeanCompCert.Ports.CDEMAbelSourceReady.nextF productionCfg after = 1 := by
  dsimp only
  have hstream := production_first_stream_step hbudget
  dsimp only at hstream
  have hvalues := productionAfterMark_first_values hbudget
  dsimp only at hvalues
  have hsecond := productionAfterMark_second_cell hbudget hdelta
  dsimp only at hsecond
  rcases productionAfterMark_cursor with ⟨_hr, _hw, hc, _hz⟩
  exact secondNextF_of_stream productionCfg _ _ _ _ hstream
    hvalues.2.1 hc hsecond

theorem secondE_of_stream (c : Cfg) (before after : AState)
    (dp dn : Nat) (hstream : InteriorStreamStepSpec c dp dn before after)
    (hnextF : nextF c before = 1) : after.regs rE = 0 := by
  rw [hstream.e, hnextF]
  decide

set_option maxRecDepth 4096 in
theorem production_second_e
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    after.regs rE = 0 := by
  dsimp only
  have hstream := production_first_stream_step hbudget
  dsimp only at hstream
  have hvalues := productionAfterMark_first_values hbudget
  dsimp only at hvalues
  exact secondE_of_stream productionCfg _ _ _ _ hstream hvalues.2.1

set_option maxRecDepth 4096 in
theorem production_second_dPos
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps)
    (hdelta : Ref.deltaF productionCfg.kBound 2 = 0) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    nextDPos productionCfg after = 0 := by
  dsimp only
  rw [nextDPos, production_second_nextF hbudget hdelta,
    production_second_e hbudget]
  decide

set_option maxRecDepth 4096 in
theorem production_second_dNeg
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps)
    (hdelta : Ref.deltaF productionCfg.kBound 2 = 0) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    nextDNeg productionCfg after = 0 := by
  dsimp only
  rw [nextDNeg, production_second_nextF hbudget hdelta,
    production_second_e hbudget]
  decide

theorem secondTv_of_stream (c : Cfg) (before after : AState)
    (dp dn : Nat) (hstream : InteriorStreamStepSpec c dp dn before after)
    (htv : before.regs rTv = 0) (hdp : dp = 0) (hdn : dn = 0) :
    after.regs rTv = 0 := by
  rw [hstream.tv, htv, hdp, hdn]

set_option maxRecDepth 4096 in
theorem production_second_tv
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    after.regs rTv = 0 := by
  dsimp only
  have hstream := production_first_stream_step hbudget
  dsimp only at hstream
  have hvalues := productionAfterMark_first_values hbudget
  dsimp only at hvalues
  rcases productionAfterMark_source_seed with
    ⟨_hf, _ht, _ht2, _he, htv, _hk, _hdp, _hdn, _hzero⟩
  exact secondTv_of_stream productionCfg _ _ _ _ hstream htv
    hvalues.2.2.1 hvalues.2.2.2

set_option maxRecDepth 4096 in
/-- Exact scalar values at the second entry, assembled only from compact
scalar declarations. -/
theorem production_second_source_values
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps)
    (hdelta : Ref.deltaF productionCfg.kBound 2 = 0) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    SecondSourceValues after := by
  dsimp only
  exact
    { key := production_second_key hbudget
      t := production_second_t hbudget
      t2 := production_second_t2 hbudget
      nextF := production_second_nextF hbudget hdelta
      e := production_second_e hbudget
      dPos := production_second_dPos hbudget hdelta
      dNeg := production_second_dNeg hbudget hdelta
      tv := production_second_tv hbudget }

structure SecondWideValues (after : AState) : Prop where
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) = 0
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) = 0
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) = 0

/-- Named second accumulation entry.  Downstream bridges use this opaque
boundary instead of asking the elaborator to unify through the production
marking trace. -/
def productionSecondState : AState :=
  bodySchedule productionCfg productionFirstIdx
    (productionCfg.bsSteps - 1)
    (bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve)

structure SecondAggregateZeros (after : AState) : Prop where
  variation : after.regs rTv = 0
  uPos : AddWide.wval (after.regs rUpLo, after.regs rUpHi) = 0
  uNeg : AddWide.wval (after.regs rUnLo, after.regs rUnHi) = 0
  v : AddWide.wval (after.regs rVLo, after.regs rVHi) = 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The zero first delta leaves both directed wide sums at zero. -/
theorem production_second_wide_values
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    SecondWideValues after := by
  let st := bodyIterFrom productionCfg productionCfg.sieveLen
    productionCfg.markSteps productionAfterSieve
  let after := bodySchedule productionCfg productionFirstIdx
    (productionCfg.bsSteps - 1) st
  have hschedule0 := production_first_schedule hbudget
  dsimp only at hschedule0
  have hfull := hschedule0.1
  have hvalues0 := productionAfterMark_first_values hbudget
  dsimp only at hvalues0
  rcases productionAfterMark_wide_seed with ⟨hup0, hun0, hv0, _hround0⟩
  have hup : AddWide.wval (st.regs rUpLo, st.regs rUpHi) = 0 := hup0
  have hun : AddWide.wval (st.regs rUnLo, st.regs rUnHi) = 0 := hun0
  have hv : AddWide.wval (st.regs rVLo, st.regs rVHi) = 0 := hv0
  exact
    { uPos := by
        rw [hfull.uPos, hup, hvalues0.2.2.1]
        simp only [Nat.zero_mul, Nat.zero_add]
      uNeg := by
        rw [hfull.uNeg, hun, hvalues0.2.2.2]
        simp only [Nat.zero_mul, Nat.zero_add]
      v := by
        rw [hfull.v, hv, hvalues0.2.2.1, hvalues0.2.2.2]
        simp only [Nat.zero_add, Nat.zero_mul] }

theorem production_second_aggregate_zeros
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    SecondAggregateZeros productionSecondState := by
  have htv0 := production_second_tv hbudget
  dsimp only at htv0
  have hwide0 := production_second_wide_values hbudget
  dsimp only at hwide0
  exact
    { variation := htv0
      uPos := hwide0.uPos
      uNeg := hwide0.uNeg
      v := hwide0.v }

set_option maxRecDepth 4096 in
/-- All numerical no-wrap conditions for the second active cell. -/
theorem production_second_bounds
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps)
    (hdelta : Ref.deltaF productionCfg.kBound 2 = 0) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    InteriorNextBounds productionCfg after := by
  let st := bodyIterFrom productionCfg productionCfg.sieveLen
    productionCfg.markSteps productionAfterSieve
  let after := bodySchedule productionCfg productionFirstIdx
    (productionCfg.bsSteps - 1) st
  have hs0 := production_second_source_values hbudget hdelta
  dsimp only at hs0
  have hs : SecondSourceValues after := hs0
  have hw0 := production_second_wide_values hbudget
  dsimp only at hw0
  have hw : SecondWideValues after := hw0
  exact
    { key_word := by rw [hs.key]; decide
      t_word := by rw [hs.t]; decide
      double_word := by rw [hs.t]; decide
      t2_word := by rw [hs.t2, hs.t]; decide
      delta_sum_word := by rw [hs.dPos, hs.dNeg]; decide
      tv_word := by rw [hs.tv, hs.dPos, hs.dNeg]; decide
      ceil_word := by rw [hs.key]; decide
      scale_plus_sqrt_word := by
        have hsqrt : Nat.sqrt 2 = 1 :=
          sqrt_eq_of_square_bounds 2 1 (by decide) (by decide)
        rw [hs.key, hsqrt]
        decide
      uPos_fit := by rw [hw.uPos, hs.dPos]; simp [AddWide.B128]
      uNeg_fit := by rw [hw.uNeg, hs.dNeg]; simp [AddWide.B128] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- The first complete active cell enters the second cell with the full
source-facing invariant. -/
theorem production_second_entry
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps)
    (hdelta : Ref.deltaF productionCfg.kBound 2 = 0) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    FirstEntryInv productionCfg after := by
  let st := bodyIterFrom productionCfg productionCfg.sieveLen
    productionCfg.markSteps productionAfterSieve
  let after := bodySchedule productionCfg productionFirstIdx
    (productionCfg.bsSteps - 1) st
  have hentry0 := productionAfterMark_firstEntry hbudget
  dsimp only at hentry0
  have hentry : FirstEntryInv productionCfg st := hentry0
  have hschedule0 := production_first_schedule hbudget
  dsimp only at hschedule0
  have hschedule :
      OuterFullAccSpec productionCfg (nextKey st)
          (nextDPos productionCfg st) (nextDNeg productionCfg st)
          (nextCeil productionCfg st) (nextFloor productionCfg st)
          (exactRoot productionCfg.wScale (nextKey st))
          (nextDPos productionCfg st + nextDNeg productionCfg st) st after ∧
        ProductionCellCursorSpec productionCfg (st.regs rC) (st.regs rR)
          (st.regs rW) after := hschedule0
  rcases productionAfterMark_cursor with ⟨_hr0, _hw0, hc0, _hz0⟩
  have hc : st.regs rC = 0 := hc0
  have hnext0 := production_second_bounds hbudget hdelta
  dsimp only at hnext0
  have hnext : InteriorNextBounds productionCfg after := hnext0
  exact interior_firstEntry_of_full productionCfg productionFirstIdx
    (productionCfg.bsSteps - 1) st (nextKey st)
    (nextDPos productionCfg st) (nextDNeg productionCfg st)
    (nextCeil productionCfg st) (nextFloor productionCfg st)
    (exactRoot productionCfg.wScale (nextKey st))
    (nextDPos productionCfg st + nextDNeg productionCfg st)
    (st.regs rC) (st.regs rR) (st.regs rW) hentry hschedule.1
    hschedule.2 rfl rfl (by rw [hc]; decide) (by decide) hnext

end LeanCompCert.Ports.CDEMAbelProductionSecondEntry

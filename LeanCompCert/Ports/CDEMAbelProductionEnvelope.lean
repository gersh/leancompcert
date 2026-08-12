import LeanCompCert.Ports.CDEMAbelProductionSecondEntry

/-! # Uniform production envelope for the CDEM Abel scan

The cell-specific opening proofs establish the exact initial state.  The
remaining five-billion-cell telescope should not repeat those proofs with one
numeral per cell.  This module isolates the deliberately coarse bounds that
are sufficient for every later machine guard.

At the entry for key `k`, at most `k - 1` increments have been accumulated.
If every signed floor-convolution jump has total magnitude at most `K`, then
the total variation is at most `(k - 1) * K`.  Both directed reciprocal sums
are at most the same quantity times `W`, because `ceil (W / k)` and
`floor (W / k)` are at most `W`.  At the production values these bounds are
below one word and two limbs respectively, with several orders of magnitude
of headroom.
-/

namespace LeanCompCert.Ports.CDEMAbelProductionEnvelope

set_option maxRecDepth 10000

open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.SqrtEquiv
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelBisection
open LeanCompCert.Ports.CDEMAbelOuterSchedule
open LeanCompCert.Ports.CDEMAbelOuterReady
open LeanCompCert.Ports.CDEMAbelSourceReady
open LeanCompCert.Ports.CDEMAbelSourceTelescope
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelMarkTermination
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionFirstSchedule
open LeanCompCert.Ports.CDEMAbelProductionFirstEntry
open LeanCompCert.Ports.CDEMAbelProductionSecondEntry
open LeanCompCert.Ports.CDEMAbelProductionMarkState
open LeanCompCert.Ports.CDEMAbelProductionInactiveWide
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor

/-- Aggregate bounds before the cell whose key is `nextKey st`. -/
structure ProductionAggregateEnvelope (st : AState) : Prop where
  variation : st.regs rTv ≤ (nextKey st - 1) * productionCfg.kBound
  uPos : AddWide.wval (st.regs rUpLo, st.regs rUpHi) ≤
    (nextKey st - 1) * productionCfg.kBound * productionCfg.wScale
  uNeg : AddWide.wval (st.regs rUnLo, st.regs rUnHi) ≤
    (nextKey st - 1) * productionCfg.kBound * productionCfg.wScale
  v : AddWide.wval (st.regs rVLo, st.regs rVHi) ≤
    (nextKey st - 1) * productionCfg.kBound * productionCfg.wScale

theorem production_nextCeil_le (st : AState) (hk : 0 < nextKey st) :
    nextCeil productionCfg st ≤ productionCfg.wScale := by
  unfold nextCeil
  apply Nat.div_le_of_le_mul
  dsimp [productionCfg]
  omega

theorem production_nextFloor_le (st : AState) :
    nextFloor productionCfg st ≤ productionCfg.wScale := by
  exact Nat.div_le_self _ _

theorem production_exactRoot_le_scale (st : AState)
    (hk : 0 < nextKey st) :
    exactRoot productionCfg.wScale (nextKey st) ≤
      productionCfg.wScale := by
  apply (pred_iff_exactRoot_le productionCfg.wScale (nextKey st)
    productionCfg.wScale hk).mp
  unfold pred
  simpa using Nat.mul_le_mul_left
    (productionCfg.wScale * productionCfg.wScale) hk

/-- The global production envelope supplies every numerical premise of the
next interior source entry.  The only cell-local input is the paper bound on
the next signed jump. -/
theorem production_interiorNextBounds_of_envelope (st : AState)
    (hsqrt : SqrtStreamInv st) (hkpos : 0 < nextKey st)
    (hkey : nextKey st ≤ productionKMax)
    (hdelta : nextDPos productionCfg st + nextDNeg productionCfg st ≤
      productionCfg.kBound)
    (henv : ProductionAggregateEnvelope st) :
    InteriorNextBounds productionCfg st := by
  have ht : st.regs rT ≤ 70710 := by
    apply Nat.le_trans
    · exact le_sqrt_of_sq_le hsqrt.lower
    · exact production_sqrt_le (nextKey st) hkey
  have hsqrtKey : Nat.sqrt (nextKey st) ≤ 70710 :=
    production_sqrt_le (nextKey st) hkey
  have hceil := production_nextCeil_le st hkpos
  have hfloor := production_nextFloor_le st
  refine
    { key_word := by
        exact Nat.lt_of_le_of_lt hkey (by decide)
      t_word := by
        exact Nat.lt_of_le_of_lt (Nat.add_le_add_right ht 1) (by decide)
      double_word := by
        have h : 2 * (st.regs rT + 1) + 1 ≤ 2 * 70711 + 1 := by omega
        exact Nat.lt_of_le_of_lt h (by decide)
      t2_word := by
        rw [hsqrt.nextSquare]
        have hq : st.regs rT + 1 ≤ 70711 := by omega
        have hsq := Nat.mul_le_mul hq hq
        have hsum :
            (st.regs rT + 1) * (st.regs rT + 1) +
                (2 * (st.regs rT + 1) + 1) ≤
              70711 * 70711 + (2 * 70711 + 1) := by
          exact Nat.add_le_add hsq (by omega)
        exact Nat.lt_of_le_of_lt hsum (by decide)
      delta_sum_word := by
        exact Nat.lt_of_le_of_lt hdelta (by decide)
      tv_word := by
        calc
          st.regs rTv +
              (nextDPos productionCfg st + nextDNeg productionCfg st) ≤
              (nextKey st - 1) * productionCfg.kBound +
                productionCfg.kBound := Nat.add_le_add henv.variation hdelta
          _ ≤ productionKMax * productionCfg.kBound := by
            dsimp [productionKMax]
            have heq :
                (nextKey st - 1) * productionCfg.kBound +
                    productionCfg.kBound =
                  nextKey st * productionCfg.kBound := by
              calc
                _ = ((nextKey st - 1) + 1) * productionCfg.kBound := by
                  rw [Nat.add_mul, Nat.one_mul]
                _ = _ := by rw [Nat.sub_add_cancel hkpos]
            rw [heq]
            exact Nat.mul_le_mul_right _ hkey
          _ < M := by decide
      ceil_word := by
        calc
          productionCfg.wScale - 1 + nextKey st ≤
              productionCfg.wScale - 1 + productionKMax :=
            Nat.add_le_add_left hkey _
          _ < M := by decide
      scale_plus_sqrt_word := by
        exact Nat.lt_of_le_of_lt
          (Nat.add_le_add_left hsqrtKey productionCfg.wScale) (by decide)
      uPos_fit := by
        calc
          AddWide.wval (st.regs rUpLo, st.regs rUpHi) +
              nextDPos productionCfg st * nextCeil productionCfg st ≤
              (nextKey st - 1) * productionCfg.kBound *
                  productionCfg.wScale +
                productionCfg.kBound * productionCfg.wScale := by
            exact Nat.add_le_add henv.uPos
              (Nat.mul_le_mul
                (Nat.le_trans (Nat.le_add_right _ _) hdelta) hceil)
          _ ≤ productionKMax * productionCfg.kBound *
                productionCfg.wScale := by
            have heq :
                (nextKey st - 1) * productionCfg.kBound +
                    productionCfg.kBound =
                  nextKey st * productionCfg.kBound := by
              calc
                _ = ((nextKey st - 1) + 1) * productionCfg.kBound := by
                  rw [Nat.add_mul, Nat.one_mul]
                _ = _ := by rw [Nat.sub_add_cancel hkpos]
            calc
              (nextKey st - 1) * productionCfg.kBound *
                    productionCfg.wScale +
                  productionCfg.kBound * productionCfg.wScale =
                  ((nextKey st - 1) * productionCfg.kBound +
                    productionCfg.kBound) * productionCfg.wScale := by
                    rw [Nat.add_mul]
              _ = nextKey st * productionCfg.kBound *
                    productionCfg.wScale := by rw [heq]
              _ ≤ _ := Nat.mul_le_mul_right _
                (Nat.mul_le_mul_right _ hkey)
          _ < AddWide.B128 := by decide
      uNeg_fit := by
        calc
          AddWide.wval (st.regs rUnLo, st.regs rUnHi) +
              nextDNeg productionCfg st * nextFloor productionCfg st ≤
              (nextKey st - 1) * productionCfg.kBound *
                  productionCfg.wScale +
                productionCfg.kBound * productionCfg.wScale := by
            exact Nat.add_le_add henv.uNeg
              (Nat.mul_le_mul
                (Nat.le_trans (Nat.le_add_left _ _) hdelta) hfloor)
          _ ≤ productionKMax * productionCfg.kBound *
                productionCfg.wScale := by
            have heq :
                (nextKey st - 1) * productionCfg.kBound +
                    productionCfg.kBound =
                  nextKey st * productionCfg.kBound := by
              calc
                _ = ((nextKey st - 1) + 1) * productionCfg.kBound := by
                  rw [Nat.add_mul, Nat.one_mul]
                _ = _ := by rw [Nat.sub_add_cancel hkpos]
            calc
              (nextKey st - 1) * productionCfg.kBound *
                    productionCfg.wScale +
                  productionCfg.kBound * productionCfg.wScale =
                  ((nextKey st - 1) * productionCfg.kBound +
                    productionCfg.kBound) * productionCfg.wScale := by
                    rw [Nat.add_mul]
              _ = nextKey st * productionCfg.kBound *
                    productionCfg.wScale := by rw [heq]
              _ ≤ _ := Nat.mul_le_mul_right _
                (Nat.mul_le_mul_right _ hkey)
          _ < AddWide.B128 := by decide }

/-- The aggregate envelope also proves the last wide-add guard once the
first and middle bisection rounds are known to preserve `V`. -/
theorem production_final_v_fit_of_envelope (idx : Nat) (st : AState)
    (hkpos : 0 < nextKey st) (hkey : nextKey st ≤ productionKMax)
    (hdelta : nextDPos productionCfg st + nextDNeg productionCfg st ≤
      productionCfg.kBound)
    (henv : ProductionAggregateEnvelope st)
    (hv :
      let current := bodyIter productionCfg idx
        (productionCfg.bsSteps - 1)
        (arun idx st productionCfg.body)
      AddWide.wval (current.regs rVLo, current.regs rVHi) =
        AddWide.wval (st.regs rVLo, st.regs rVHi)) :
    let current := bodyIter productionCfg idx
      (productionCfg.bsSteps - 1)
      (arun idx st productionCfg.body)
    AddWide.wval (current.regs rVLo, current.regs rVHi) +
      (nextDPos productionCfg st + nextDNeg productionCfg st) *
        exactRoot productionCfg.wScale (nextKey st) < AddWide.B128 := by
  have hroot := production_exactRoot_le_scale st hkpos
  dsimp only at hv ⊢
  rw [hv]
  calc
    AddWide.wval (st.regs rVLo, st.regs rVHi) +
          (nextDPos productionCfg st + nextDNeg productionCfg st) *
            exactRoot productionCfg.wScale (nextKey st) ≤
        (nextKey st - 1) * productionCfg.kBound *
            productionCfg.wScale +
          productionCfg.kBound * productionCfg.wScale := by
      exact Nat.add_le_add henv.v (Nat.mul_le_mul hdelta hroot)
    _ ≤ productionKMax * productionCfg.kBound *
          productionCfg.wScale := by
      have heq :
          (nextKey st - 1) * productionCfg.kBound +
              productionCfg.kBound =
            nextKey st * productionCfg.kBound := by
        calc
          _ = ((nextKey st - 1) + 1) * productionCfg.kBound := by
            rw [Nat.add_mul, Nat.one_mul]
          _ = _ := by rw [Nat.sub_add_cancel hkpos]
      calc
        (nextKey st - 1) * productionCfg.kBound *
              productionCfg.wScale +
            productionCfg.kBound * productionCfg.wScale =
            ((nextKey st - 1) * productionCfg.kBound +
              productionCfg.kBound) * productionCfg.wScale := by
                rw [Nat.add_mul]
        _ = nextKey st * productionCfg.kBound *
              productionCfg.wScale := by rw [heq]
        _ ≤ _ := Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right _ hkey)
    _ < AddWide.B128 := by decide

/-- A source entry satisfying the global envelope can execute its production
cell without a separately trusted final-accumulator guard. -/
theorem production_bodySchedule_of_envelope (idx : Nat) (st : AState)
    (hidxM : idx < M) (hsieve : productionCfg.sieveLen ≤ idx)
    (hWnext : st.regs rW + productionCfg.segLen < M)
    (hstartR : st.regs rR = productionCfg.markSteps +
      st.regs rC * (productionCfg.bsSteps + 1))
    (hentry : FirstEntryInv productionCfg st)
    (hkey : nextKey st ≤ productionKMax)
    (hdelta : nextDPos productionCfg st + nextDNeg productionCfg st ≤
      productionCfg.kBound)
    (henv : ProductionAggregateEnvelope st) :
    OuterFullAccSpec productionCfg (nextKey st)
        (nextDPos productionCfg st) (nextDNeg productionCfg st)
        (nextCeil productionCfg st) (nextFloor productionCfg st)
        (exactRoot productionCfg.wScale (nextKey st))
        (nextDPos productionCfg st + nextDNeg productionCfg st)
        st (bodySchedule productionCfg idx
          (productionCfg.bsSteps - 1) st) ∧
      ProductionCellCursorSpec productionCfg (st.regs rC) (st.regs rR)
        (st.regs rW) (bodySchedule productionCfg idx
          (productionCfg.bsSteps - 1) st) := by
  have hv := bodySchedule_preFinal_v_of_entry productionCfg
    idx st rfl (by decide) hidxM (by decide)
    hsieve (by decide) (by decide) (by omega) (by decide) (by decide)
    (by decide) hstartR hentry hkey
  have haccFit := production_final_v_fit_of_envelope idx st hentry.key_pos
    hkey hdelta henv hv
  exact bodySchedule_production_of_entry productionCfg idx st
    rfl (by decide) hidxM (by decide) hsieve (by decide)
    (by decide) (by omega) (by decide) (by decide) (by decide) hWnext
    hstartR hentry hkey haccFit

private theorem prefix_budget_step {a d k K : Nat} (hk : 0 < k)
    (ha : a ≤ (k - 1) * K) (hd : d ≤ K) : a + d ≤ k * K := by
  apply Nat.le_trans (Nat.add_le_add ha hd)
  calc
    (k - 1) * K + K = ((k - 1) + 1) * K := by
      rw [Nat.add_mul, Nat.one_mul]
    _ = k * K := by rw [Nat.sub_add_cancel hk]
    _ ≤ k * K := Nat.le_refl _

/-- One successful interior cell preserves the aggregate envelope.  This is
the induction step needed by the eventual whole-window telescope; it depends
only on the per-cell jump bound, not on any concrete cell numeral. -/
theorem production_aggregateEnvelope_step (before after : AState)
    (dp dn root : Nat) (hkpos : 0 < nextKey before)
    (hdelta : dp + dn ≤ productionCfg.kBound)
    (hroot : root ≤ productionCfg.wScale)
    (henv : ProductionAggregateEnvelope before)
    (hfull : OuterFullAccSpec productionCfg (nextKey before) dp dn
      (nextCeil productionCfg before) (nextFloor productionCfg before)
      root (dp + dn) before after)
    (hkey : nextKey after = nextKey before + 1) :
    ProductionAggregateEnvelope after := by
  have hceil := production_nextCeil_le before hkpos
  have hfloor := production_nextFloor_le before
  have hdp : dp ≤ productionCfg.kBound :=
    Nat.le_trans (Nat.le_add_right _ _) hdelta
  have hdn : dn ≤ productionCfg.kBound :=
    Nat.le_trans (Nat.le_add_left _ _) hdelta
  have hdpw : dp * nextCeil productionCfg before ≤
      productionCfg.kBound * productionCfg.wScale :=
    Nat.mul_le_mul hdp hceil
  have hdnw : dn * nextFloor productionCfg before ≤
      productionCfg.kBound * productionCfg.wScale :=
    Nat.mul_le_mul hdn hfloor
  have hdw : (dp + dn) * root ≤
      productionCfg.kBound * productionCfg.wScale :=
    Nat.mul_le_mul hdelta hroot
  constructor
  · rw [hfull.tv, hkey]
    rw [Nat.add_sub_cancel, Nat.add_assoc]
    exact prefix_budget_step hkpos henv.variation hdelta
  · rw [hfull.uPos, hkey]
    rw [Nat.add_sub_cancel,
      Nat.mul_assoc (nextKey before) productionCfg.kBound
        productionCfg.wScale]
    have henvPos : AddWide.wval
        (before.regs rUpLo, before.regs rUpHi) ≤
        (nextKey before - 1) *
          (productionCfg.kBound * productionCfg.wScale) := by
      rw [← Nat.mul_assoc]
      exact henv.uPos
    exact prefix_budget_step
      (K := productionCfg.kBound * productionCfg.wScale)
      hkpos henvPos hdpw
  · rw [hfull.uNeg, hkey]
    rw [Nat.add_sub_cancel,
      Nat.mul_assoc (nextKey before) productionCfg.kBound
        productionCfg.wScale]
    have henvNeg : AddWide.wval
        (before.regs rUnLo, before.regs rUnHi) ≤
        (nextKey before - 1) *
          (productionCfg.kBound * productionCfg.wScale) := by
      rw [← Nat.mul_assoc]
      exact henv.uNeg
    exact prefix_budget_step
      (K := productionCfg.kBound * productionCfg.wScale)
      hkpos henvNeg hdnw
  · rw [hfull.v, hkey]
    rw [Nat.add_sub_cancel,
      Nat.mul_assoc (nextKey before) productionCfg.kBound
        productionCfg.wScale]
    have henvV : AddWide.wval
        (before.regs rVLo, before.regs rVHi) ≤
        (nextKey before - 1) *
          (productionCfg.kBound * productionCfg.wScale) := by
      rw [← Nat.mul_assoc]
      exact henv.v
    exact prefix_budget_step
      (K := productionCfg.kBound * productionCfg.wScale)
      hkpos henvV hdw

/-- The exact zero first increment seeds the uniform envelope at key `2`. -/
theorem production_second_aggregateEnvelope
    (hbudget : 1 + compactMarkBudget productionCfg ≤
      productionCfg.markSteps) :
    let st := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    let after := bodySchedule productionCfg productionFirstIdx
      (productionCfg.bsSteps - 1) st
    ProductionAggregateEnvelope after := by
  let st := bodyIterFrom productionCfg productionCfg.sieveLen
    productionCfg.markSteps productionAfterSieve
  let after := bodySchedule productionCfg productionFirstIdx
    (productionCfg.bsSteps - 1) st
  have hkey := production_second_key hbudget
  dsimp only at hkey
  have htv := production_second_tv hbudget
  dsimp only at htv
  have hu := production_second_wide_values hbudget
  dsimp only at hu
  have hs := production_first_schedule hbudget
  dsimp only at hs
  have hvalues0 := productionAfterMark_first_values hbudget
  dsimp only at hvalues0
  rcases productionAfterMark_wide_seed with ⟨_hup, _hun, hv0, _hround⟩
  have hv := hs.1.v
  rw [hv0, hvalues0.2.2.1, hvalues0.2.2.2] at hv
  simp only [Nat.zero_add, Nat.zero_mul] at hv
  constructor
  · rw [htv, hkey]
    exact Nat.zero_le _
  · rw [hu.uPos, hkey]
    exact Nat.zero_le _
  · rw [hu.uNeg, hkey]
    exact Nat.zero_le _
  · rw [hv, hkey]
    exact Nat.zero_le _

end LeanCompCert.Ports.CDEMAbelProductionEnvelope

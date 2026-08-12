import LeanCompCert.Ports.CDEMAbelInactiveWideBody
import LeanCompCert.Ports.CDEMAbelProductionInactiveMark

/-! # Production wide sums after the finite inactive CDEM prefixes -/

namespace LeanCompCert.Ports.CDEMAbelProductionInactiveWide

open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelSieveScheduledTable
open LeanCompCert.Ports.CDEMAbelMarkSchedule
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor
open LeanCompCert.Ports.CDEMAbelProductionSieveState
open LeanCompCert.Ports.CDEMAbelProductionSourceSeed
open LeanCompCert.Ports.CDEMAbelProductionInactiveSieve
open LeanCompCert.Ports.CDEMAbelProductionInactiveMark
open LeanCompCert.Ports.CDEMAbelInactiveBody
open LeanCompCert.Ports.CDEMAbelInactiveSieve
open LeanCompCert.Ports.CDEMAbelInactiveMark
open LeanCompCert.Ports.CDEMAbelInactiveWideBody

attribute [local irreducible] bodySieveIter bodyIterFrom

theorem bodySieveIter_inactive_wide (c : Cfg) (count : Nat) (st : AState)
    (hcount : count ≤ c.sieveLen) (hsieveM : c.sieveLen < M)
    (hsinkM : c.sink < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hzero : st.regs rZero = 0)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveBodyWideSpec st (bodySieveIter c count st) := by
  induction count with
  | zero =>
      rw [bodySieveIter_zero]
      exact ⟨rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      let current := bodySieveIter c n st
      have hs := bodySieveIter_inactive_source c n st (by omega) hsieveM
        hsinkM hword harrword hzero hk hWM hsum hceilFit
      have hnlt : n < c.sieveLen := by omega
      have hgate := (selectors_sieve_run c n current
        (Nat.lt_trans hnlt hsieveM) hsieveM hnlt).2.2.2.1
      have hstep := inactiveBodyRun_wide c n current hgate
        (hs.1.zero.trans hzero) hsinkM hs.2.1 hs.2.2
        (by rw [hs.1.k]; exact hk) hWM
        (by rw [hs.1.dPos, hs.1.dNeg]; exact hsum)
        (by rw [hs.1.k]; exact hceilFit)
      rw [bodySieveIter_succ, body_run_eq_inactiveBodyRun]
      exact ih (by omega) |>.trans hstep

theorem bodyIterFrom_mark_inactive_wide (c : Cfg) (start count : Nat)
    (st : AState) (hcount : count ≤ c.markSteps)
    (hidxM : start + count < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ start) (hmarkM : c.markSteps < M)
    (hmarkPeriod : c.markSteps < c.period) (hperiodM : c.period < M)
    (hsegM : c.segLen < M) (hsinkM : c.sink < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hR : st.regs rR = 0) (hzero : st.regs rZero = 0)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveBodyWideSpec st (bodyIterFrom c start count st) := by
  induction count with
  | zero =>
      rw [bodyIterFrom_zero]
      exact ⟨rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      let current := bodyIterFrom c start n st
      have hs := bodyIterFrom_mark_inactive_source c start n st
        (by omega) (by omega) hsieveM hsieve hmarkM hmarkPeriod hperiodM
        hsegM hsinkM hword harrword hR hzero hk hWM hsum hceilFit
      have hselected := selectors_mark_run c (start + n) current
        (by omega) hsieveM (by omega) hmarkM
        (by rw [hs.2.2.2]; omega)
      have hstep := inactiveBodyRun_wide c (start + n) current
        hselected.2.2.2.1 (hs.1.zero.trans hzero) hsinkM hs.2.1 hs.2.2.1
        (by rw [hs.1.k]; exact hk) hWM
        (by rw [hs.1.dPos, hs.1.dNeg]; exact hsum)
        (by rw [hs.1.k]; exact hceilFit)
      rw [bodyIterFrom_succ, body_run_eq_inactiveBodyRun]
      exact ih (by omega) (by omega) |>.trans hstep

/-- All three wide sums and the bisection round counter remain at their
physical zero seed at the first production accumulation iteration. -/
theorem productionAfterMark_wide_seed :
    let out := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    AddWide.wval (out.regs rUpLo, out.regs rUpHi) = 0 ∧
      AddWide.wval (out.regs rUnLo, out.regs rUnHi) = 0 ∧
      AddWide.wval (out.regs rVLo, out.regs rVHi) = 0 ∧
      out.regs rKr = 0 := by
  rcases production_source_seed with
    ⟨_hf, _he, hkr, _hc, hdp, hdn, _ht, _ht2, hupl, huph, hunl,
      hunh, hvl, hvh, _htv⟩
  rcases production_source_seed_controls with ⟨hzero, hk⟩
  have hentryWord := sieveEntry_word productionCfg
  have hsieve := bodySieveIter_inactive_wide productionCfg
    productionCfg.sieveLen (sieveEntry productionCfg) (by omega)
    (by change 17142466 < M; decide)
    (by change 1199417 < M; decide) hentryWord.1 hentryWord.2 hzero
    (by rw [hk]; decide)
    (by change 1000000000000000000 < M; decide)
    (by rw [hdp, hdn]; decide) (by rw [hk]; decide)
  have hsieveEq : bodySieveIter productionCfg productionCfg.sieveLen
      (sieveEntry productionCfg) = productionAfterSieve := by
    rw [productionAfterSieve, ← bodySieveIter_eq_fold]
  rw [hsieveEq] at hsieve
  rcases productionAfterSieve_source_seed with
    ⟨_hfS, _htS, _ht2S, _heS, _htvS, hkS, hdpS, hdnS, hzeroS⟩
  have hwords := productionAfterSieve_state
  have hmark := bodyIterFrom_mark_inactive_wide productionCfg
    productionCfg.sieveLen productionCfg.markSteps productionAfterSieve
    (by omega) (by change 25987624 < M; decide)
    (by change 17142466 < M; decide) (by omega)
    (by change 8845158 < M; decide)
    (by change 8845158 < 70845158; decide)
    (by change 70845158 < M; decide)
    (by change 1000000 < M; decide)
    (by change 1199417 < M; decide) hwords.2.1 hwords.2.2
    productionAfterSieve_cursor.1 hzeroS (by rw [hkS]; decide)
    (by change 1000000000000000000 < M; decide)
    (by rw [hdpS, hdnS]; decide) (by rw [hkS]; decide)
  have hall := hsieve.trans hmark
  exact ⟨by rw [hall.uPos, hupl, huph]; rfl,
    by rw [hall.uNeg, hunl, hunh]; rfl,
    by rw [hall.v, hvl, hvh]; rfl,
    hall.round.trans hkr⟩

end LeanCompCert.Ports.CDEMAbelProductionInactiveWide

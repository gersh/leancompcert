import LeanCompCert.Ports.CDEMAbelInactiveSieve
import LeanCompCert.Ports.CDEMAbelProductionSourceSeed
import LeanCompCert.Ports.CDEMAbelProductionSieveCursor

/-! # Production source state after the finite CDEM sieve prefix -/

namespace LeanCompCert.Ports.CDEMAbelProductionInactiveSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelSieveScheduledTable
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor
open LeanCompCert.Ports.CDEMAbelProductionSourceSeed
open LeanCompCert.Ports.CDEMAbelInactiveBody
open LeanCompCert.Ports.CDEMAbelInactiveSieve

/-- The actual 17,142,466-iteration emitted sieve computation preserves the
source stream seeded by the physical initializer. -/
theorem productionAfterSieve_source_seed :
    productionAfterSieve.regs rF = 0 ∧
      productionAfterSieve.regs rT = 1 ∧
      productionAfterSieve.regs rT2 = 4 ∧
      productionAfterSieve.regs rE = 0 ∧
      productionAfterSieve.regs rTv = 0 ∧
      productionAfterSieve.regs rK = 1 ∧
      productionAfterSieve.regs rDp = 0 ∧
      productionAfterSieve.regs rDn = 0 ∧
      productionAfterSieve.regs rZero = 0 := by
  rcases production_source_seed with
    ⟨hf, he, _hkr, _hc, hdp, hdn, ht, ht2, _hupl, _huph, _hunl,
      _hunh, _hvl, _hvh, htv⟩
  rcases production_source_seed_controls with ⟨hzero, hk⟩
  have hwords := sieveEntry_word productionCfg
  have hiter := bodySieveIter_inactive_source productionCfg
    productionCfg.sieveLen (sieveEntry productionCfg) (by omega)
    (by change 17142466 < M; decide)
    (by change 1199417 < M; decide) hwords.1 hwords.2 hzero
    (by rw [hk]; decide)
    (by change 1000000000000000000 < M; decide)
    (by rw [hdp, hdn]; decide)
    (by rw [hk]; decide)
  have heq : bodySieveIter productionCfg productionCfg.sieveLen
      (sieveEntry productionCfg) = productionAfterSieve := by
    rw [productionAfterSieve, ← bodySieveIter_eq_fold]
  rw [heq] at hiter
  exact ⟨hiter.1.f.trans hf,
    hiter.1.t.trans ht,
    hiter.1.t2.trans ht2,
    hiter.1.e.trans he,
    hiter.1.tv.trans htv,
    hiter.1.k.trans hk,
    hiter.1.dPos.trans hdp,
    hiter.1.dNeg.trans hdn,
    hiter.1.zero.trans hzero⟩

end LeanCompCert.Ports.CDEMAbelProductionInactiveSieve

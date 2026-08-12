import LeanCompCert.Ports.CDEMAbelInactiveMark
import LeanCompCert.Ports.CDEMAbelProductionInactiveSieve
import LeanCompCert.Ports.CDEMAbelProductionMarkState

/-! # Production source state after the finite CDEM marking prefix -/

namespace LeanCompCert.Ports.CDEMAbelProductionInactiveMark

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor
open LeanCompCert.Ports.CDEMAbelProductionSieveState
open LeanCompCert.Ports.CDEMAbelProductionMarkState
open LeanCompCert.Ports.CDEMAbelProductionInactiveSieve
open LeanCompCert.Ports.CDEMAbelInactiveMark

set_option maxRecDepth 4096 in
/-- The complete production marking computation preserves the physical
initializer's source stream and inactive latches. -/
theorem productionAfterMark_source_seed :
    let out := bodyIterFrom productionCfg productionCfg.sieveLen
      productionCfg.markSteps productionAfterSieve
    out.regs rF = 0 ∧ out.regs rT = 1 ∧ out.regs rT2 = 4 ∧
      out.regs rE = 0 ∧ out.regs rTv = 0 ∧ out.regs rK = 1 ∧
      out.regs rDp = 0 ∧ out.regs rDn = 0 ∧
      out.regs rZero = 0 := by
  rcases productionAfterSieve_source_seed with
    ⟨hf, ht, ht2, he, htv, hk, hdp, hdn, hzero⟩
  have hwords := productionAfterSieve_state
  have hiter := bodyIterFrom_mark_inactive_source productionCfg
    productionCfg.sieveLen productionCfg.markSteps productionAfterSieve
    (by omega)
    (by change 25987624 < M; decide)
    (by change 17142466 < M; decide) (by omega)
    (by change 8845158 < M; decide)
    (by change 8845158 < 70845158; decide)
    (by change 70845158 < M; decide)
    (by change 1000000 < M; decide)
    (by change 1199417 < M; decide) hwords.2.1 hwords.2.2
    productionAfterSieve_cursor.1 hzero
    (by rw [hk]; decide)
    (by change 1000000000000000000 < M; decide)
    (by rw [hdp, hdn]; decide)
    (by rw [hk]; decide)
  exact ⟨hiter.1.f.trans hf,
    hiter.1.t.trans ht,
    hiter.1.t2.trans ht2,
    hiter.1.e.trans he,
    hiter.1.tv.trans htv,
    hiter.1.k.trans hk,
    hiter.1.dPos.trans hdp,
    hiter.1.dNeg.trans hdn,
    hiter.1.zero.trans hzero⟩

end LeanCompCert.Ports.CDEMAbelProductionInactiveMark

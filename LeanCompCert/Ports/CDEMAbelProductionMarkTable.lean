import LeanCompCert.Ports.CDEMAbelProductionSieveCursor

/-! # Production CDEM resident marking table -/

namespace LeanCompCert.Ports.CDEMAbelProductionMarkTable

open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor

/-- The named post-sieve state is the exact changing-index source fold. -/
theorem productionAfterSieve_eq_fold :
    productionAfterSieve =
      (List.range productionCfg.sieveLen).foldl
        (fun s idx =>
          LeanCompCert.Verified.ArrayFoldBridge.arun idx s productionCfg.body)
        (sieveEntry productionCfg) := by
  rfl

/-- Named-state form of the complete resident table. -/
theorem productionAfterSieve_table_all :
    ∀ d, d < productionCfg.k1 →
      productionAfterSieve.arr (d + productionCfg.muBase) =
        Ref.muCodeFor productionCfg.kBound d := by
  rw [productionAfterSieve_eq_fold]
  exact productionAfterSieve_table

/-- The live-divisor view consumed by the marking cursor. -/
theorem productionAfterSieve_table_live :
    ∀ d, 1 ≤ d → d ≤ productionCfg.kBound →
      productionAfterSieve.arr (d + productionCfg.muBase) =
        Ref.muCodeFor productionCfg.kBound d := by
  intro d _ hd
  exact productionAfterSieve_table_all d (by
    unfold Cfg.k1
    omega)

end LeanCompCert.Ports.CDEMAbelProductionMarkTable

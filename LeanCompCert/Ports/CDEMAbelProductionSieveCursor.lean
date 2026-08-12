import LeanCompCert.Ports.CDEMAbelProductionSieveMark
import LeanCompCert.Ports.CDEMAbelSieveMarkEntry

/-! # Production CDEM cursor after the scheduled sieve prefix -/

namespace LeanCompCert.Ports.CDEMAbelProductionSieveCursor

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelSieveScheduledTable
open LeanCompCert.Ports.CDEMAbelSieveMarkEntry
open LeanCompCert.Ports.CDEMAbelProductionSieveMark

def productionAfterSieve : AState :=
  (List.range productionCfg.sieveLen).foldl
    (fun s idx => arun idx s productionCfg.body) (sieveEntry productionCfg)

/-- The exact changing-index production sieve prefix leaves the first window
at origin one and its period cursor at zero. -/
theorem productionAfterSieve_cursor :
    productionAfterSieve.regs rR = 0 ∧
      productionAfterSieve.regs rW = 1 := by
  rw [productionAfterSieve, ← bodySieveIter_eq_fold]
  apply bodySieveIter_preserves_rR_rW productionCfg productionCfg.sieveLen
    (sieveEntry productionCfg) 1
  · omega
  · change 17142466 < M
    decide
  · change 0 < 70845158
    decide
  · change 70845158 < M
    decide
  · decide
  · exact (sieveEntry_rR_rW productionCfg).1
  · exact (sieveEntry_rR_rW productionCfg).2

/-- The same exact production prefix installs the finite resident Möbius code
in every live divisor cell. -/
theorem productionAfterSieve_table :
    let out := (List.range productionCfg.sieveLen).foldl
      (fun s idx => arun idx s productionCfg.body) (sieveEntry productionCfg)
    ∀ d, d < productionCfg.k1 →
      out.arr (d + productionCfg.muBase) =
        Ref.muCodeFor productionCfg.kBound d := by
  exact initialized_scheduled_sieve_full_muCodeFor productionCfg
    (by change 0 < 86; decide)
    (by change 86 < M; decide)
    (by change 17142466 < M; decide)
    (by change 1199417 < M; decide)
    production_prime_pos production_prime_word production_primes_spec

end LeanCompCert.Ports.CDEMAbelProductionSieveCursor

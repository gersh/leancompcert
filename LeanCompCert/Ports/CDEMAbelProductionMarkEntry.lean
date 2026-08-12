import LeanCompCert.Ports.CDEMAbelProductionSieveState
import LeanCompCert.Ports.CDEMAbelMarkTelescope

/-! # Production CDEM entry into the marking phase -/

namespace LeanCompCert.Ports.CDEMAbelProductionMarkEntry

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor
open LeanCompCert.Ports.CDEMAbelProductionSieveState

/-- The first real production marking iteration is represented by the pure
marking cursor.  Its prerequisites come only from the two small post-sieve
certificates, keeping the large prime computation out of this elaboration. -/
theorem productionFirstMark_rep :
    MarkStateRep productionCfg 1 1
      (MarkState.first productionCfg productionAfterSieve)
      (arun productionCfg.sieveLen productionAfterSieve
        productionCfg.body) := by
  apply body_first_markState_rep productionCfg productionCfg.sieveLen
    productionAfterSieve 1
  · change 17142466 < M
    decide
  · change 17142466 < M
    decide
  · omega
  · change 0 < 8845158
    decide
  · change 8845158 < M
    decide
  · change 70845158 < M
    decide
  · exact productionAfterSieve_cursor.1
  · exact productionAfterSieve_state.1
  · change 0 < 1000000
    decide
  · change 0 < 199330
    decide
  · change 1000000 < M
    decide
  · change 199330 < M
    decide
  · change 199417 < M
    decide
  · change 1199417 < M
    decide
  · exact productionAfterSieve_cursor.2
  · change 1 < M
    decide

end LeanCompCert.Ports.CDEMAbelProductionMarkEntry

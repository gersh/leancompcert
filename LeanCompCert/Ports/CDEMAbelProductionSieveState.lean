import LeanCompCert.Ports.CDEMAbelProductionSieveCursor

/-! # Production CDEM machine state after the scheduled sieve prefix -/

namespace LeanCompCert.Ports.CDEMAbelProductionSieveState

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelSieveReady
open LeanCompCert.Ports.CDEMAbelSieveScheduledTable
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveMark
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor

/-- The exact production sieve prefix preserves the compiled zero register and
keeps every resident array cell inside the machine word modulus.  This state
fact is isolated from the literal prime certificate so later marking proofs do
not need to elaborate both large arguments in one process. -/
theorem productionAfterSieve_state :
    productionAfterSieve.regs rZero = 0 ∧
      ∀ j, productionAfterSieve.arr j < M := by
  rcases bodySieveIter_invariant productionCfg productionCfg.sieveLen
    (sieveEntry productionCfg) (initialSieveModel productionCfg)
    (sieveEntry_preRep productionCfg)
    (initialSieveModel_cursor productionCfg
      (by change 0 < 86; decide) production_prime_pos
      (by change 86 < M; decide) production_prime_word)
    (initialSieveModel_table productionCfg
      (by change 86 < M; decide) production_prime_word)
    (by simp [sieveRank, initialSieveModel]) (by omega)
    (by change 17142466 < M; decide)
    (by change 86 < M; decide)
    (by change 1199417 < M; decide) with
    ⟨finalModel, hfinalRep, _, _, _⟩
  rw [productionAfterSieve, ← bodySieveIter_eq_fold]
  exact ⟨hfinalRep.zero, hfinalRep.arrWord⟩

end LeanCompCert.Ports.CDEMAbelProductionSieveState

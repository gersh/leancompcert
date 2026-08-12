import LeanCompCert.Ports.CDEMAbelProductionInactiveSieve

/-! # Production CDEM sieve window frame -/

namespace LeanCompCert.Ports.CDEMAbelProductionSieveWindow

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelSieveTelescope
open LeanCompCert.Ports.CDEMAbelSieveReady
open LeanCompCert.Ports.CDEMAbelSieveTable
open LeanCompCert.Ports.CDEMAbelSieveScheduledTable
open LeanCompCert.Ports.CDEMAbelInactiveSieve
open LeanCompCert.Ports.CDEMAbelProductionCertificate
open LeanCompCert.Ports.CDEMAbelProductionSieveMark
open LeanCompCert.Ports.CDEMAbelProductionSieveCursor

theorem production_sieveEntry_window_zero :
    (sieveEntry productionCfg).arr productionCfg.winBase = 0 := by
  unfold sieveEntry Cfg.init
  rw [arun_append, cdem_seedRegs_arr]
  rw [cdem_storeLits_arr 0 productionCfg.winBase initialAState
    productionCfg.primeCells]
  · rw [cdem_cellWrite_of_forall_ne]
    · rfl
    · intro x hx
      rcases List.mem_map.mp hx with ⟨row, hrow, rfl⟩
      have hi := List.mem_zipIdx' hrow
      have hlt : row.2 < 86 := by
        simpa [Cfg.pn, productionCfg] using hi.1
      unfold Cfg.primeBase Cfg.winBase Cfg.muBase Cfg.k1
      simp only [Nat.zero_add]
      have hpn : productionCfg.pn = 86 := by decide
      have hkBound : productionCfg.kBound = 199330 := rfl
      rw [hpn, hkBound]
      omega
  · exact primeCells_word productionCfg (by decide)
      (by
        intro p hp
        change p < 18446744073709551616
        simp [productionCfg] at hp
        omega)

/-- The entire 17,142,466-step resident sieve leaves the first marking-window
cell at its physical zero initializer. -/
theorem productionAfterSieve_window_zero :
    productionAfterSieve.arr productionCfg.winBase = 0 := by
  have hframe := bodySieveIter_winBase_frame productionCfg
    productionCfg.sieveLen (sieveEntry productionCfg)
    (initialSieveModel productionCfg) (sieveEntry_preRep productionCfg)
    (initialSieveModel_cursor productionCfg
      (by change 0 < 86; decide) production_prime_pos
      (by change 86 < M; decide) production_prime_word)
    (initialSieveModel_table productionCfg
      (by change 86 < M; decide) production_prime_word)
    (by simp [sieveRank, initialSieveModel]) (by omega)
    (by change 17142466 < M; decide)
    (by change 86 < M; decide)
    (by change 1199417 < M; decide)
    (by change 0 < 1000000; decide)
  rw [productionAfterSieve, ← bodySieveIter_eq_fold]
  exact hframe.trans production_sieveEntry_window_zero

end LeanCompCert.Ports.CDEMAbelProductionSieveWindow

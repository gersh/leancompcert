import LeanCompCert.Ports.CDEMAbelProductionCertificate

/-! # Production CDEM sieve-to-marking certificate -/

namespace LeanCompCert.Ports.CDEMAbelProductionSieveMark

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelProductionCertificate

set_option maxRecDepth 4096 in
/-- The finite square-root bound used to construct the production prime base. -/
theorem production_sqrt_eq : Nat.sqrt productionCfg.kBound = 446 := by
    change Nat.sqrt 199330 = 446
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro hn
      have hq : 447 ≤ Nat.sqrt 199330 := by omega
      have hmul : 447 * 447 ≤ Nat.sqrt 199330 * Nat.sqrt 199330 :=
        Nat.mul_le_mul hq hq
      have hs := Nat.sqrt_le 199330
      omega
    · apply Nat.le_of_not_gt
      intro hn
      have hs : Nat.sqrt 199330 + 1 ≤ 446 := by omega
      have hmul :
          (Nat.sqrt 199330 + 1) * (Nat.sqrt 199330 + 1) ≤ 446 * 446 :=
        Nat.mul_le_mul hs hs
      have hlt := Nat.lt_succ_sqrt 199330
      rw [Nat.succ_eq_add_one] at hlt
      omega

set_option maxRecDepth 4096 in
/-- The literal prime list in the compiled production configuration agrees
with the finite verified constructor used by the source computation. -/
theorem production_primes_spec :
    productionCfg.primes = Ref.muPrimes productionCfg.kBound := by
  rw [Ref.muPrimes, production_sqrt_eq]
  rfl

theorem production_prime_pos : ∀ p ∈ productionCfg.primes, 0 < p := by
  intro p hp
  rw [production_primes_spec] at hp
  have hprime := LeanCompCert.Verified.PackedSieve.PrimeBase.prime hp
  exact Nat.zero_lt_of_lt hprime.two_le

theorem production_prime_word : ∀ p ∈ productionCfg.primes, p < M := by
  intro p hp
  rw [production_primes_spec] at hp
  have hmem :=
    (LeanCompCert.Verified.PackedSieve.PrimeBase.ofTrialDivision
      (Nat.sqrt productionCfg.kBound)).mem_iff p |>.mp hp
  rw [production_sqrt_eq] at hmem
  change p ≤ 446 ∧ LeanCompCert.Verified.PackedSieve.IsPrime p at hmem
  have hpBound : p ≤ 446 := by
    exact hmem.1
  have hM : 446 < M := by decide
  omega

end LeanCompCert.Ports.CDEMAbelProductionSieveMark

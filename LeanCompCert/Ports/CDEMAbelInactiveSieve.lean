import LeanCompCert.Ports.CDEMAbelInactiveBody
import LeanCompCert.Ports.CDEMAbelSieveScheduledTable

/-! # Finite inactive source frame through the CDEM sieve prefix -/

namespace LeanCompCert.Ports.CDEMAbelInactiveSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelSieveScheduledTable
open LeanCompCert.Ports.CDEMAbelInactiveBody

theorem bodySieveIter_zero (c : Cfg) (st : AState) :
    bodySieveIter c 0 st = st := rfl

theorem bodySieveIter_succ (c : Cfg) (n : Nat) (st : AState) :
    bodySieveIter c (n + 1) st =
      arun n (bodySieveIter c n st) c.body := rfl

attribute [local irreducible] bodySieveIter

/-- Simultaneous source and word invariant for the changing-index finite
sieve computation. -/
theorem bodySieveIter_inactive_source (c : Cfg) (count : Nat) (st : AState)
    (hcount : count ≤ c.sieveLen) (hsieveM : c.sieveLen < M)
    (hsinkM : c.sink < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hzero : st.regs rZero = 0)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveBodySourceSpec st (bodySieveIter c count st) ∧
      (∀ j, (bodySieveIter c count st).regs j < M) ∧
      ∀ j, (bodySieveIter c count st).arr j < M := by
  induction count with
  | zero =>
      rw [bodySieveIter_zero]
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        hword, harrword⟩
  | succ n ih =>
      let current := bodySieveIter c n st
      have hnlt : n < c.sieveLen := by omega
      have hnM : n < M := Nat.lt_trans hnlt hsieveM
      have hi := ih (by omega)
      have hgate := (selectors_sieve_run c n current hnM hsieveM hnlt).2.2.2.1
      have hstep := inactiveBodyRun_source c n current hgate
        (hi.1.zero.trans hzero) hsinkM hi.2.1 hi.2.2
        (by rw [hi.1.k]; exact hk) hWM
        (by rw [hi.1.dPos, hi.1.dNeg]; exact hsum)
        (by rw [hi.1.k]; exact hceilFit)
      let next := inactiveBodyRun c n current
      have hsource : InactiveBodySourceSpec st next := hi.1.trans hstep
      have hnextWord : (∀ j, next.regs j < M) ∧ ∀ j, next.arr j < M :=
        inactiveBodyRun_word c n current hi.2.1 hi.2.2
      rw [bodySieveIter_succ, body_run_eq_inactiveBodyRun]
      exact ⟨hsource, hnextWord⟩

end LeanCompCert.Ports.CDEMAbelInactiveSieve

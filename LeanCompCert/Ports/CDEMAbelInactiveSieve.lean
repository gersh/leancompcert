import LeanCompCert.Ports.CDEMAbelInactiveBody
import LeanCompCert.Ports.CDEMAbelSieveScheduledTable

/-! # Finite inactive source frame through the CDEM sieve prefix -/

namespace LeanCompCert.Ports.CDEMAbelInactiveSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelSieveInit
open LeanCompCert.Ports.CDEMAbelSieveTelescope
open LeanCompCert.Ports.CDEMAbelSieveReady
open LeanCompCert.Ports.CDEMAbelSieveTable
open LeanCompCert.Ports.CDEMAbelSieveSchedule
open LeanCompCert.Ports.CDEMAbelSieveScheduledTable
open LeanCompCert.Ports.CDEMAbelInactiveBody

theorem bodySieveIter_zero (c : Cfg) (st : AState) :
    bodySieveIter c 0 st = st := rfl

theorem bodySieveIter_succ (c : Cfg) (n : Nat) (st : AState) :
    bodySieveIter c (n + 1) st =
      arun n (bodySieveIter c n st) c.body := rfl

attribute [local irreducible] bodySieveIter

theorem body_sieve_state_step_inactiveRun (c : Cfg) (idx : Nat)
    (machine : AState) (model : SieveState)
    (hrep : SievePreRep model machine) (hidxM : idx < M)
    (hsieveM : c.sieveLen < M) (hidx : idx < c.sieveLen)
    (hready : SieveStepReady c model) (hsinkM : c.sink < M) :
    let out := inactiveBodyRun c idx machine
    SievePreRep (resync (model.step c) out) out ∧
      (∀ j, j ≠ c.sink → out.arr j = (model.step c).arr j) := by
  rw [inactiveBodyRun]
  exact body_sieve_state_step c idx machine model hrep hidxM hsieveM hidx
    hready hsinkM

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

/-- The finite scheduled sieve cannot touch the first window cell: completed
rows write below `winBase`, and incomplete rows write only to the sink. -/
theorem bodySieveIter_winBase_frame (c : Cfg) (count : Nat)
    (machine : AState) (model : SieveState)
    (hrep : SievePreRep model machine) (hcursor : SieveCursorInv c model)
    (htable : SieveTableInv c model) (hrank : sieveRank c model = 0)
    (hcount : count ≤ c.sieveLen) (hsieveM : c.sieveLen < M)
    (hpnM : c.pn < M) (hsinkM : c.sink < M)
    (hsegPos : 0 < c.segLen) :
    (bodySieveIter c count machine).arr c.winBase = machine.arr c.winBase := by
  induction count with
  | zero => rw [bodySieveIter_zero]
  | succ n ih =>
      have hnlt : n < c.sieveLen := by omega
      rcases bodySieveIter_invariant c n machine model hrep hcursor htable
        hrank (by omega) hsieveM hpnM hsinkM with
        ⟨preModel, hpreRep, hpreCursor, hpreTable, hpreRank⟩
      let before := bodySieveIter c n machine
      let after := inactiveBodyRun c n before
      have hready := sieve_ready_of_rank c preModel hpreCursor hpreRank
        hnlt hpnM hsinkM
      have hstep := body_sieve_state_step_inactiveRun c n before preModel hpreRep
        (Nat.lt_trans hnlt hsieveM) hsieveM hnlt hready hsinkM
      have hnBound : preModel.n < c.k1 := by
        have hmul : preModel.n * c.pn < c.k1 * c.pn := by
          calc
            preModel.n * c.pn ≤ sieveRank c preModel := by simp [sieveRank]
            _ = n := hpreRank
            _ < c.sieveLen := hnlt
            _ = c.k1 * c.pn := rfl
        exact Nat.lt_of_mul_lt_mul_right hmul
      have haddr : c.winBase ≠ preModel.n + c.muBase := by
        unfold Cfg.winBase
        omega
      have hsink : c.winBase ≠ c.sink := by
        unfold Cfg.sink
        omega
      have hmodel : (preModel.step c).arr c.winBase =
          preModel.arr c.winBase := by
        by_cases hlast : preModel.pj = c.pn - 1
        · simp [SieveState.step, hlast, writeCell, haddr]
        · simp [SieveState.step, hlast, writeCell, hsink]
      have hbefore : before.arr c.winBase = preModel.arr c.winBase := by
        exact congrFun hpreRep.arr c.winBase
      rw [bodySieveIter_succ, body_run_eq_inactiveBodyRun]
      calc
        after.arr c.winBase = (preModel.step c).arr c.winBase :=
          hstep.2 c.winBase hsink
        _ = preModel.arr c.winBase := hmodel
        _ = before.arr c.winBase := hbefore.symm
        _ = machine.arr c.winBase := ih (by omega)

end LeanCompCert.Ports.CDEMAbelInactiveSieve

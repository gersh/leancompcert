import LeanCompCert.Ports.CDEMAbelInactiveBody
import LeanCompCert.Ports.CDEMAbelMarkTelescope

/-! # Finite inactive source frame through a CDEM marking prefix -/

namespace LeanCompCert.Ports.CDEMAbelInactiveMark

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMarkSchedule
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelInactiveBody

theorem bodyIterFrom_zero (c : Cfg) (start : Nat) (st : AState) :
    bodyIterFrom c start 0 st = st := rfl

theorem bodyIterFrom_succ (c : Cfg) (start n : Nat) (st : AState) :
    bodyIterFrom c start (n + 1) st =
      LeanCompCert.Verified.ArrayFoldBridge.arun (start + n)
        (bodyIterFrom c start n st) c.body := rfl

attribute [local irreducible] bodyIterFrom

/-- The telescope consumes only the finite selector computation at each
marking step.  Cursor refinements can supply that selector premise without
reducing the production-size trace. -/
theorem bodyIterFrom_inactive_source (c : Cfg) (start count : Nat)
    (st : AState)
    (hgate : ∀ n, n < count →
      (LeanCompCert.Verified.ArrayFoldBridge.arun (start + n)
        (bodyIterFrom c start n st) c.selectors).regs 43 = 0)
    (hsinkM : c.sink < M) (hword : ∀ j, st.regs j < M)
    (harrword : ∀ j, st.arr j < M) (hzero : st.regs rZero = 0)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveBodySourceSpec st (bodyIterFrom c start count st) ∧
      (∀ j, (bodyIterFrom c start count st).regs j < M) ∧
      ∀ j, (bodyIterFrom c start count st).arr j < M := by
  induction count with
  | zero =>
      rw [bodyIterFrom_zero]
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        hword, harrword⟩
  | succ n ih =>
      let current := bodyIterFrom c start n st
      have hi := ih (fun i hi => hgate i (by omega))
      have hstep := inactiveBodyRun_source c (start + n) current
        (hgate n (by omega)) (hi.1.zero.trans hzero) hsinkM hi.2.1 hi.2.2
        (by rw [hi.1.k]; exact hk) hWM
        (by rw [hi.1.dPos, hi.1.dNeg]; exact hsum)
        (by rw [hi.1.k]; exact hceilFit)
      let next := inactiveBodyRun c (start + n) current
      have hsource : InactiveBodySourceSpec st next := hi.1.trans hstep
      have hnextWord : (∀ j, next.regs j < M) ∧ ∀ j, next.arr j < M :=
        inactiveBodyRun_word c (start + n) current hi.2.1 hi.2.2
      rw [bodyIterFrom_succ, body_run_eq_inactiveBodyRun]
      exact ⟨hsource, hnextWord⟩

/-- Marking-specialized telescope.  It proves the selector premise and the
period cursor together, using only the emitted selector and tail contracts. -/
theorem bodyIterFrom_mark_inactive_source (c : Cfg) (start count : Nat)
    (st : AState) (hcount : count ≤ c.markSteps)
    (hidxM : start + count < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ start) (hmarkM : c.markSteps < M)
    (hmarkPeriod : c.markSteps < c.period) (hperiodM : c.period < M)
    (hsegM : c.segLen < M) (hsinkM : c.sink < M)
    (hword : ∀ j, st.regs j < M) (harrword : ∀ j, st.arr j < M)
    (hR : st.regs rR = 0) (hzero : st.regs rZero = 0)
    (hk : 0 < st.regs rK) (hWM : c.wScale < M)
    (hsum : st.regs rDp + st.regs rDn < M)
    (hceilFit : c.wScale - 1 + st.regs rK < M) :
    InactiveBodySourceSpec st (bodyIterFrom c start count st) ∧
      (∀ j, (bodyIterFrom c start count st).regs j < M) ∧
      (∀ j, (bodyIterFrom c start count st).arr j < M) ∧
      (bodyIterFrom c start count st).regs rR = count := by
  induction count with
  | zero =>
      rw [bodyIterFrom_zero]
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        hword, harrword, hR⟩
  | succ n ih =>
      let current := bodyIterFrom c start n st
      have hi := ih (by omega) (by omega)
      have hnMark : n < c.markSteps := by omega
      have hselected := selectors_mark_run c (start + n) current
        (by omega) hsieveM (by omega) hmarkM (by rw [hi.2.2.2]; exact hnMark)
      have hstep := inactiveBodyRun_source c (start + n) current
        hselected.2.2.2.1 (hi.1.zero.trans hzero) hsinkM hi.2.1 hi.2.2.1
        (by rw [hi.1.k]; exact hk) hWM
        (by rw [hi.1.dPos, hi.1.dNeg]; exact hsum)
        (by rw [hi.1.k]; exact hceilFit)
      let next := inactiveBodyRun c (start + n) current
      have hsource : InactiveBodySourceSpec st next := hi.1.trans hstep
      have hnextWord : (∀ j, next.regs j < M) ∧ ∀ j, next.arr j < M :=
        inactiveBodyRun_word c (start + n) current hi.2.1 hi.2.2.1
      have hcursor : next.regs rR = n + 1 := by
        rw [inactiveBodyRun_mark_cursor c (start + n) current
          hselected.2.1
          (by rw [hi.2.2.2]; exact Nat.lt_of_le_of_lt (by omega) hmarkPeriod)
          (by rw [hi.2.2.2]; exact Nat.lt_of_le_of_lt (by omega) hmarkM)
          hperiodM hsegM hi.2.1 hi.2.2.1,
          hi.2.2.2]
      rw [bodyIterFrom_succ, body_run_eq_inactiveBodyRun]
      exact ⟨hsource, hnextWord.1, hnextWord.2, hcursor⟩

end LeanCompCert.Ports.CDEMAbelInactiveMark

import LeanCompCert.Ports.CDEMAbelMarkPlane

/-! # Compact-budget entry point for the complete CDEM marking plane -/

namespace LeanCompCert.Ports.CDEMAbelMarkPlaneBudget

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelMarkTelescope
open LeanCompCert.Ports.CDEMAbelMarkReady
open LeanCompCert.Ports.CDEMAbelMarkTermination
open LeanCompCert.Ports.CDEMAbelMarkPlane

/-- A non-dependent compact-budget wrapper around the exact full marking
window theorem.  Keeping `first_cursorInv` out of the caller-facing premise
prevents production configurations from being unfolded during proof-term
unification. -/
theorem bodyIterFrom_full_mark_window_eq_deltaF_of_compact_budget (c : Cfg)
    (start : Nat) (st : LeanCompCert.Verified.ArrayState.AState) (w : Nat)
    (hfirst : MarkStateRep c w 1 (MarkState.first c st)
      (LeanCompCert.Verified.ArrayFoldBridge.arun start st c.body))
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
    (hword : ∀ j, j < c.segLen → st.arr (j + c.winBase) < M)
    (hidxM : start + c.markSteps < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ start) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hsegPos : 0 < c.segLen)
    (hsegM : c.segLen < M) (hkTwo : 2 ≤ c.kBound) (hkM : c.kBound < M)
    (hcompact : 1 + compactMarkBudget c ≤ c.markSteps)
    (hkNextM : c.kBound + 1 < M) (hsumM : c.segLen + c.kBound < M)
    (hsinkM : c.sink < M) (hperiodM : c.period < M) (hwM : w < M) :
    let out := bodyIterFrom c start c.markSteps st
    ∀ j, j < c.segLen →
      out.arr (j + c.winBase) =
        (st.arr (j + c.winBase) + Ref.deltaF c.kBound (w + j)) % M := by
  have hkPos : 0 < c.kBound := by omega
  have hremaining := first_remaining_le_compactMarkBudget c st w htable hkTwo
  have hbudget :
      1 + remaining c w (MarkState.first c st)
        (first_cursorInv c st htable hkPos).divisorPos ≤ c.markSteps :=
    Nat.le_trans (Nat.add_le_add_left hremaining 1) hcompact
  exact bodyIterFrom_full_mark_window_eq_deltaF c start st w hfirst htable
    hword hidxM hsieveM hsieve hmarkPos hmarkM hsegPos hsegM hkPos hkM
    hbudget hkNextM hsumM hsinkM hperiodM hwM

/-- State-facing companion to the plane theorem.  It exposes the exact
cursor, window, zero register, and pure marking model after the complete
changing-index block, including terminal slack iterations. -/
theorem bodyIterFrom_full_mark_state (c : Cfg) (start : Nat)
    (st : LeanCompCert.Verified.ArrayState.AState) (w : Nat)
    (hfirst : MarkStateRep c w 1 (MarkState.first c st)
      (LeanCompCert.Verified.ArrayFoldBridge.arun start st c.body))
    (htable : ∀ d, 1 ≤ d → d ≤ c.kBound →
      st.arr (d + c.muBase) = Ref.muCodeFor c.kBound d)
    (hidxM : start + c.markSteps < M) (hsieveM : c.sieveLen < M)
    (hsieve : c.sieveLen ≤ start) (hmarkPos : 0 < c.markSteps)
    (hmarkM : c.markSteps < M) (hsegPos : 0 < c.segLen)
    (hsegM : c.segLen < M) (hkPos : 0 < c.kBound) (hkM : c.kBound < M)
    (hkNextM : c.kBound + 1 < M) (hsumM : c.segLen + c.kBound < M)
    (hsinkM : c.sink < M) (hperiodM : c.period < M) (hwM : w < M) :
    MarkStateRep c w c.markSteps
      ((MarkState.first c st).iter c w (c.markSteps - 1))
      (bodyIterFrom c start c.markSteps st) := by
  have hrep := bodyIterFrom_markState_from_start_ready c start
    (c.markSteps - 1) st w hfirst htable (by omega) (by omega)
    hsieveM hsieve hmarkM hsegPos hsegM hkPos hkM hkNextM hsumM hsinkM
    hperiodM hwM
  have hleft : 1 + (c.markSteps - 1) = c.markSteps := by omega
  have hright : c.markSteps - 1 + 1 = c.markSteps := by omega
  rw [hleft, hright] at hrep
  exact hrep

/-- Machine-word closure for an arbitrary changing-index body block. -/
theorem bodyIterFrom_word (c : Cfg) (start n : Nat)
    (st : LeanCompCert.Verified.ArrayState.AState)
    (hregs : ∀ j, st.regs j < M) (harr : ∀ j, st.arr j < M) :
    (∀ j, (bodyIterFrom c start n st).regs j < M) ∧
      ∀ j, (bodyIterFrom c start n st).arr j < M := by
  induction n with
  | zero => exact ⟨hregs, harr⟩
  | succ n ih =>
      rw [bodyIterFrom]
      exact LeanCompCert.Verified.ArrayFoldBridge.arun_word
        (start + n) c.body (bodyIterFrom c start n st) ih.1 ih.2

end LeanCompCert.Ports.CDEMAbelMarkPlaneBudget

import LeanCompCert.Ports.DirichletLadderExternalSafetyDenotation
import LeanCompCert.Ports.DirichletLadderExternalSafetyStep

/-! Telescope from sticky machine acceptance to every decoded record guard. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.DirichletLadder

private def storeFree : AInstr → Bool
  | .store _ _ => false
  | _ => true

private theorem arun_arr_frame (idx : Nat) : ∀ (l : List AInstr) (s : AState),
    l.all storeFree = true → (arun idx s l).arr = s.arr := by
  intro l
  induction l with
  | nil => intro s _; rfl
  | cons i rest ih =>
      intro s h
      rw [List.all_cons, Bool.and_eq_true] at h
      rw [arun_cons, ih _ h.2]
      cases i with
      | scalar instr => exact AState.writeReg_arr _ _ _
      | load d a => exact AState.writeReg_arr _ _ _
      | store a v => simp [storeFree] at h

theorem guardBody_arr (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (guardBody c)).arr = s.arr :=
  arun_arr_frame idx (guardBody c) s (by rfl)

private theorem fold_guards_zero_back
    (c : Cfg) (arr : Nat → Nat) (xs : List Nat) (s : AState)
    (hsArr : s.arr = arr)
    (hword : ∀ j, s.regs j < M) (harr : ∀ j, s.arr j < M)
    (hstatic : StaticBounds c)
    (hindices : ∀ idx ∈ xs, idx < c.records)
    (hout : BadZero
      (xs.foldl (fun state index => arun index state (guardBody c)) s)) :
    BadZero s ∧ ∀ idx ∈ xs, RecordSafe c arr idx := by
  induction xs generalizing s with
  | nil =>
      exact ⟨hout, by simp⟩
  | cons idx rest ih =>
      let s' := arun idx s (guardBody c)
      have hw' := arun_word idx (guardBody c) s hword harr
      have hs'Arr : s'.arr = arr := by
        rw [show s'.arr = s.arr from guardBody_arr c idx s, hsArr]
      have htail := ih s' hs'Arr hw'.1 hw'.2
        (by intro j hj; exact hindices j (by simp [hj])) (by
          simpa [s'] using hout)
      have hhead := guardBody_zero_back c arr idx s hsArr hword harr hstatic
        (hindices idx (by simp)) htail.1
      refine ⟨hhead.1, ?_⟩
      intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact hhead.2
      · exact htail.2 j hj

/-- An accepting fixed-width audit proves every safety precondition used by
the historical ladder checker.  This is a symbolic fold proof: it does not
evaluate any production record or assume analytic GRH evidence. -/
theorem allRecordsSafe_of_machineAccepts
    (c : Cfg) (arr : Nat → Nat)
    (words : ∀ k, arr k < M) (hstatic : StaticBounds c)
    (haccept : MachineAccepts c arr) :
    AllRecordsSafe c arr := by
  have hentry : WordState (symbolicEntry c arr) := by
    change WordState (initialAStateWithArray arr)
    exact initialAStateWithArray_word arr words
  have hloop : WordState (symbolicLoop c arr) := by
    exact arunFold_word (guardBody c) (List.range c.records)
      (symbolicEntry c arr) hentry
  have hfinish : BadZero (symbolicLoop c arr) :=
    finishBlock_zero_back (symbolicLoop c arr) hloop.1 hloop.2 (by
      simpa [MachineAccepts, symbolicFinal, program] using haccept)
  have htelescope := fold_guards_zero_back c arr (List.range c.records)
    (symbolicEntry c arr) (by
      change (initialAStateWithArray arr).arr = arr
      rfl) hentry.1 hentry.2 hstatic
    (by intro idx hidx; simpa using hidx) (by
      simpa [symbolicLoop, program] using hfinish)
  intro idx hidx
  exact htelescope.2 idx (by simpa using hidx)

end LeanCompCert.Ports.DirichletLadderExternalSafety

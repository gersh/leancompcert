import LeanCompCert.Ports.CDEMAbelOuterSchedule

namespace LeanCompCert.Ports.CDEMAbelOuterReady

open LeanCompCert
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports
open LeanCompCert.Ports.CDEMAbelScan
open LeanCompCert.Ports.CDEMAbelOuterSchedule

theorem bodyIter_succ_start (c : Cfg) (idx n : Nat) (st : AState) :
    bodyIter c idx n (arun idx st c.body) = bodyIter c idx (n + 1) st := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change arun idx (bodyIter c idx n (arun idx st c.body)) c.body =
        arun idx (bodyIter c idx (n + 1) st) c.body
      exact congrArg (fun s => arun idx s c.body) ih

theorem bodySchedule_eq_bodyIter (c : Cfg) (idx middleCount : Nat)
    (st : AState) :
    bodySchedule c idx middleCount st = bodyIter c idx (middleCount + 2) st := by
  rw [bodySchedule, bodyIter_succ_start]
  rfl

structure CursorTraceSpec (n : Nat) (before after : AState) : Prop where
  cursor : after.regs rR = before.regs rR + n
  window : after.regs rW = before.regs rW

theorem bodyIter_cursor_contracts (c : Cfg) (idx n : Nat) (st : AState)
    (hcontract : ∀ i, i < n →
      let before := bodyIter c idx i st
      let after := bodyIter c idx (i + 1) st
      after.regs rR = before.regs rR + 1 ∧
        after.regs rW = before.regs rW) :
    CursorTraceSpec n st (bodyIter c idx n st) := by
  induction n with
  | zero =>
      exact
        { cursor := by simp [bodyIter]
          window := rfl }
  | succ n ih =>
      have hpre : ∀ i, i < n →
          let before := bodyIter c idx i st
          let after := bodyIter c idx (i + 1) st
          after.regs rR = before.regs rR + 1 ∧
            after.regs rW = before.regs rW :=
        fun i hi => hcontract i (by omega)
      have hi := ih hpre
      have hs := hcontract n (by omega)
      dsimp only at hs
      exact
        { cursor := by rw [hs.1, hi.cursor]; omega
          window := hs.2.trans hi.window }

theorem bodySchedule_cursor_of_contracts (c : Cfg) (idx middleCount : Nat)
    (st : AState)
    (hcontract : ∀ i, i < middleCount + 2 →
      let before := bodyIter c idx i st
      let after := bodyIter c idx (i + 1) st
      after.regs rR = before.regs rR + 1 ∧
        after.regs rW = before.regs rW) :
    let out := bodySchedule c idx middleCount st
    out.regs rR = st.regs rR + (middleCount + 2) ∧
      out.regs rW = st.regs rW := by
  have ht := bodyIter_cursor_contracts c idx (middleCount + 2) st hcontract
  rw [bodySchedule_eq_bodyIter]
  exact ⟨ht.cursor, ht.window⟩

end LeanCompCert.Ports.CDEMAbelOuterReady

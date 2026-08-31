import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceBodyMonotone
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceCounterMonotoneMiddleFrames

/-! Literal body framing for the two weak-loop fields needed by the counter telescope. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

def historicalBodyBeforeCopies (c : Cfg) : List AInstr :=
  historicalEarly c ++ historicalPostEarlyHead c ++
  historicalMiddleLate c ++ historicalStateMux c

theorem historicalBody_eq_load_before_copies (c : Cfg) :
    c.bodyBlock = historicalLoad c ++ historicalBodyBeforeCopies c ++
      historicalStateCopies c := by
  rw [historicalBody_eq_load_early_post]
  simp only [historicalBodyBeforeCopies, historicalPostEarly,
    historicalPostEarlyTail, historicalUpdateTail, List.append_assoc]

set_option maxHeartbeats 1000000 in
theorem historicalBodyBeforeCopies_frame22
    (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalBodyBeforeCopies c)).regs 22 = s.regs 22 := by
  simp only [historicalBodyBeforeCopies, historicalPostEarlyHead,
    historicalMiddleLate, arun_append]
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 22
      (historicalStateMux c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 22
      (historicalLateFlags c) (by rfl),
    historicalMiddleFlags_frame22,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 22
      (historicalMainFlags c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 22
      (historicalDerived c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 22
      (historicalEarly c) (by rfl)]

set_option maxHeartbeats 1000000 in
theorem historicalBodyBeforeCopies_frame28
    (c : Cfg) (idx : Nat) (s : AState) :
    (arun idx s (historicalBodyBeforeCopies c)).regs 28 = s.regs 28 := by
  simp only [historicalBodyBeforeCopies, historicalPostEarlyHead,
    historicalMiddleLate, arun_append]
  rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 28
      (historicalStateMux c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 28
      (historicalLateFlags c) (by rfl),
    historicalMiddleFlags_frame28,
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 28
      (historicalMainFlags c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 28
      (historicalDerived c) (by rfl),
    LeanCompCert.Verified.ArrayRegFrame.arun_frame idx 28
      (historicalEarly c) (by rfl)]

theorem historicalStateCopies_prev_fields
    (c : Cfg) (idx : Nat) (s : AState) :
    let out := arun idx s (historicalStateCopies c)
    out.regs rPrevBlk = s.regs 22 ∧ out.regs rPrevLast = s.regs 28 := by
  have h := historicalStateCopies_result c idx (s.regs 21) (s.regs 22)
    (s.regs 25) (s.regs 97) (s.regs 28) (s.regs 32) (s.regs 158) s
    rfl rfl rfl rfl rfl rfl rfl
  exact ⟨h.2.1, h.2.2.2.2.1⟩

theorem historicalBody_prev_fields
    (c : Cfg) (idx : Nat) (s : AState) :
    let loaded := arun idx s (historicalLoad c)
    let out := arun idx s c.bodyBlock
    out.regs rPrevBlk = loaded.regs 22 ∧
      out.regs rPrevLast = loaded.regs 28 := by
  let loaded := arun idx s (historicalLoad c)
  let beforeCopies := arun idx loaded (historicalBodyBeforeCopies c)
  have loaded_eq : loaded = arun idx s (historicalLoad c) := rfl
  have before_eq : beforeCopies =
      arun idx loaded (historicalBodyBeforeCopies c) := rfl
  have hf22 := historicalBodyBeforeCopies_frame22 c idx loaded
  rw [← before_eq] at hf22
  have hf28 := historicalBodyBeforeCopies_frame28 c idx loaded
  rw [← before_eq] at hf28
  have hc := historicalStateCopies_prev_fields c idx beforeCopies
  rw [historicalBody_eq_load_before_copies, arun_append, arun_append]
  rw [← loaded_eq, ← before_eq]
  exact ⟨hc.1.trans hf22, hc.2.trans hf28⟩

end LeanCompCert.Ports.DirichletLadderExternalSafety

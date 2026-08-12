import LeanCompCert.Ports.CDEMAbelMarkBudgetCheck

namespace LeanCompCert.Ports.CDEMAbelMarkBudgetCheck

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock

def entry : RegState := initialState.set 0 (seed % M)

theorem entry_init :
    denoteInstrs 0 initialState initBlock = some entry := rfl

theorem entry_inv : Inv entry := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases h : j = 0
    · subst h
      simp only [entry, RegState.set, if_pos, Nat.mod_lt _ M_pos]
    · simp only [entry, RegState.set, if_neg h, initialState]
      exact M_pos
  · simp [entry, RegState.set, initialState]
  · simp [entry, RegState.set, initialState]

end LeanCompCert.Ports.CDEMAbelMarkBudgetCheck

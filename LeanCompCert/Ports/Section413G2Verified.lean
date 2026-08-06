import LeanCompCert.Ports.Section413G2FinalDenote
import LeanCompCert.Ports.Section413G2Sound

/-!
# End-to-end verified route for the §4.1.3 `g₂` sweep

This module is the non-circular join between the emitted program's denotation
and the transparent model's source-soundness theorem.
-/

namespace LeanCompCert.Ports.Section413G2Verified

open LeanCompCert
open LeanCompCert.Ports.Section413G2Program

/-- A zero denotation of the emitted array program proves the independently
defined reference sweep Boolean. -/
theorem denote_zero_sound (c : Cfg)
    (hc : LeanCompCert.Ports.Section413G2Sound.Admissible c)
    (hzero : (g2Program c).denote = some 0) :
    LeanCompCert.Ports.Section413Sweep.g2SweepOK
      c.rounds c.checkLo c.cap = true := by
  have hden := LeanCompCert.Ports.Section413G2Denote.g2Program_denote c
    hc.toDenote
  rw [hden] at hzero
  have ht : c.tFlag = 0 := by injection hzero
  exact LeanCompCert.Ports.Section413G2Sound.tFlag_zero_sound c hc ht

/-- The strongest executable receipt: if the verified CCIR/LeanCompCert
evaluation returns zero, the reference sweep Boolean is true. -/
theorem compiled_zero_sound (c : Cfg)
    (hc : LeanCompCert.Ports.Section413G2Sound.Admissible c)
    (base : Int) (hBase : LeanCompCert.Verified.ArrayState.BaseOk
      (g2Program c).arrayLen base)
    (hzero :
      Option.bind
          (Verified.MemFragment.evalMCCSequence
            ((g2Program c).initialMCC base) (g2Program c).compile)
          (fun m : Verified.MemFragment.MCCState =>
            m.env ⟨(g2Program c).output + 1⟩) = some 0) :
    LeanCompCert.Ports.Section413Sweep.g2SweepOK
      c.rounds c.checkLo c.cap = true := by
  have hden := LeanCompCert.Ports.Section413G2Denote.g2Program_denote c
    hc.toDenote
  have hrun := g2Program_compiled c base hBase c.tFlag hden
  rw [hzero] at hrun
  have htInt : ((c.tFlag : Nat) : Int) = 0 := (Option.some.inj hrun).symm
  have ht : c.tFlag = 0 := by exact_mod_cast htInt
  exact LeanCompCert.Ports.Section413G2Sound.tFlag_zero_sound c hc ht

theorem production_denote_zero_sound
    (hzero : (g2Program production).denote = some 0) :
    LeanCompCert.Ports.Section413Sweep.g2SweepOK
      production.rounds production.checkLo production.cap = true :=
  denote_zero_sound production
    LeanCompCert.Ports.Section413G2Sound.production_admissible hzero

end LeanCompCert.Ports.Section413G2Verified

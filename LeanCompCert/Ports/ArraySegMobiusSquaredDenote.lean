import LeanCompCert.Ports.ArraySegMobiusSquaredSeed
import LeanCompCert.Ports.ArraySegMobiusInit

/-!
# Partial-semantics boundaries for the production squared Möbius program

The compiler theorem for an array program requires a proved source
denotation.  This file discharges the initializer and epilogue portions of
that obligation.  The loop-body theorem is deliberately separate: it must
use the production sieve schedule to prove every dynamic divisor and array
address safe, rather than infer source success backwards from a compiled run.
-/

namespace LeanCompCert.Ports.ArraySegMobiusSquaredDenote

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.MobiusSquaredResidueRealisation

/-- The residue seed block contains only literal scalar moves. -/
theorem mobiusLiveInit_denote_arun (len : Nat) (seed : MobLiveSeed)
    (s : AState) :
    denoteAInstrs len 0 s (mobiusLiveInit seed) =
      some (arun 0 s (mobiusLiveInit seed)) := by
  apply denoteAInstrs_eq_arun
  simp [mobiusLiveInit, ArraySegSieve.seed, AllDefined, ADefined]

/-- The emitted program initializer denotes its existing total-state entry. -/
theorem mobiusLiveSquaredProgram_init_denote (c : Cfg) (k : Nat)
    (seed : MobLiveSeed)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (harrayM : c.arrayLen < M) :
    denoteAInstrs (mobiusLiveSquaredProgram c k seed).arrayLen 0 initialAState
        (mobiusLiveSquaredProgram c k seed).init =
      some (combinedEntry c seed) := by
  have hcore := denote_coreInit_eq_arun c 0 initialAState hbootLe harrayM
  let mid := arun 0 initialAState c.coreInit
  have hlive := mobiusLiveInit_denote_arun c.arrayLen seed mid
  rw [mobiusLiveSquaredProgram, Cfg.program, denoteAInstrs_append, hcore]
  change denoteAInstrs c.arrayLen 0 mid (mobiusLiveInit seed) =
    some (combinedEntry c seed)
  rw [combinedEntry, arun_append]
  exact hlive

private theorem denoteAInstrs_append_intro (len idx : Nat)
    (s sm out : AState) (xs ys : List AInstr)
    (hx : denoteAInstrs len idx s xs = some sm)
    (hy : denoteAInstrs len idx sm ys = some out) :
    denoteAInstrs len idx s (xs ++ ys) = some out := by
  rw [denoteAInstrs_append, hx]
  exact hy

/-- One combined loop iteration denotes its total execution once source
safety has been established on the standalone sieve projection.  The
nonzero-candidate guard is then transported to the framed residue state. -/
theorem squaredBody_denote_arun (c : Cfg) (k len idx : Nat) {s t : AState}
    (hagree : CoreAgree s t)
    (hcore : AllDefined len idx t c.coreBody)
    (hn : (arun idx t c.coreBody).regs 65 ≠ 0) :
    denoteAInstrs len idx s (c.coreBody ++ mobiusLiveSquaredResidue k) =
      some (arun idx s (c.coreBody ++ mobiusLiveSquaredResidue k)) := by
  have hcoreS : AllDefined len idx s c.coreBody :=
    (allDefined_coreBody_congr c len idx hagree).mpr hcore
  have hcoreDenote : denoteAInstrs len idx s c.coreBody =
      some (arun idx s c.coreBody) :=
    denoteAInstrs_eq_arun len idx c.coreBody s hcoreS
  have hagreeCore : CoreAgree (arun idx s c.coreBody)
      (arun idx t c.coreBody) :=
    arun_coreBody_congr c idx hagree
  have hnS : (arun idx s c.coreBody).regs 65 ≠ 0 := by
    rw [hagreeCore.2 65 (by rfl)]
    exact hn
  have hres := mobiusLiveSquaredResidue_denote_arun k len idx
    (arun idx s c.coreBody) hnS
  calc
    denoteAInstrs len idx s (c.coreBody ++ mobiusLiveSquaredResidue k) =
        some (arun idx (arun idx s c.coreBody)
          (mobiusLiveSquaredResidue k)) :=
      denoteAInstrs_append_intro len idx s (arun idx s c.coreBody)
        (arun idx (arun idx s c.coreBody) (mobiusLiveSquaredResidue k))
        c.coreBody (mobiusLiveSquaredResidue k) hcoreDenote hres
    _ = some (arun idx s (c.coreBody ++ mobiusLiveSquaredResidue k)) :=
      congrArg some (arun_append idx c.coreBody
        (mobiusLiveSquaredResidue k) s).symm

/-- Every result slot selected by the squared epilogue lies inside the fixed
sixteen-cell result area. -/
theorem mobiusLiveEpilogue_denote_arun (c : Cfg) (s : AState)
    (harrayM : c.arrayLen < M) :
    denoteAInstrs c.arrayLen 0 s (mobiusLiveEpilogue c) =
      some (arun 0 s (mobiusLiveEpilogue c)) := by
  have h0 : c.resultBase + 0 < c.arrayLen := by
    simp only [Cfg.arrayLen]
    omega
  have hb : c.resultBase < c.arrayLen := by simpa using h0
  have h1 : c.resultBase + 1 < c.arrayLen := by
    simp only [Cfg.arrayLen]
    omega
  have h2 : c.resultBase + 2 < c.arrayLen := by
    simp only [Cfg.arrayLen]
    omega
  have h3 : c.resultBase + 3 < c.arrayLen := by
    simp only [Cfg.arrayLen]
    omega
  have h8 : c.resultBase + 8 < c.arrayLen := by
    simp only [Cfg.arrayLen]
    omega
  have hbM := Nat.lt_trans hb harrayM
  have h1M := Nat.lt_trans h1 harrayM
  have h2M := Nat.lt_trans h2 harrayM
  have h3M := Nat.lt_trans h3 harrayM
  have h8M := Nat.lt_trans h8 harrayM
  apply denoteAInstrs_eq_arun
  simp [mobiusLiveEpilogue, storeResult, AllDefined, ADefined, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, AState.writeReg,
    Nat.mod_eq_of_lt hbM, Nat.mod_eq_of_lt h1M, Nat.mod_eq_of_lt h2M,
    Nat.mod_eq_of_lt h3M, Nat.mod_eq_of_lt h8M, hb, h1, h2, h3, h8]

end LeanCompCert.Ports.ArraySegMobiusSquaredDenote

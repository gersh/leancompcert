/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413G1TableSound
import LeanCompCert.Verified.ArrayPipeline

/-!
# Compiled Section 4.1.3 G1 table producer

The historical table certificate appended a comparison against 99,999
literal cells.  That made a production data set part of Lean elaboration.
This program keeps the already verified arithmetic body and its two table
stores, but has no literal-table epilogue.  A following compiled program can
consume the resulting array through `ArrayPipeline` without materialising
the table in Lean.

The execution theorem is symbolic in `c.loopCount`: it rewrites the program
to `rawFinal`; it never reduces the production fold.
-/

namespace LeanCompCert.Ports.Section413G1TableProducer

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Section413G1Program
open LeanCompCert.Ports.Section413G1TableProgram
open LeanCompCert.Ports.Section413Sweep

def producerProgram (c : Cfg) : AProgram :=
  { regCount := LeanCompCert.Ports.Section413G1TableProgram.regCount
    arrayLen := tableArrayLen c
    loopCount := c.loopCount
    init := c.init
    body := c.body ++ tableStoreBody c
    epilogue := []
    output := rViol }

theorem producerProgram_wf (c : Cfg) : (producerProgram c).WF := by
  refine ⟨show rViol < LeanCompCert.Ports.Section413G1TableProgram.regCount
      by decide, base_init_wf c, ?_, ?_⟩
  · intro i hi
    simp only [producerProgram, List.mem_append] at hi
    exact hi.elim (base_body_wf c i) (tableStoreBody_wf c i)
  · intro i hi
    cases hi

/-- The producer started from a zero array reaches the same symbolic final
state used by the table-refinement proof.  No closed loop is evaluated. -/
theorem producer_runFromZero (c : Cfg) (hc : TableAdmissible c) :
    (producerProgram c).runFromArray (fun _ => 0) = some (rawFinal c) := by
  apply AProgram.runFromArray_eq_foldl_mem
    (p := producerProgram c)
    (P := WordInv)
    (step := fun index s => rawStep c index s)
    (fin := id)
    (arr := fun _ => 0)
    (s₀ := rawEntry c)
  · apply denoteAInstrs_eq_arun
    have hi := (LeanCompCert.Ports.Section413G1Denote.init_reaches_tInit c
      (by simp [Cfg.arrayLen]; omega)).1
    simpa [producerProgram, initialAStateWithArray, initialAState, rawEntry]
      using allDefined_mono_len (base_len_le_table_len c) c.init
        initialAState hi
  · refine ⟨LeanCompCert.Ports.Section413G1Denote.arun_regs_lt
        0 c.init initialAState ?_ ?_,
      LeanCompCert.Ports.Section413G1Denote.arun_arr_lt
        0 c.init initialAState ?_ ?_⟩ <;>
      simp [initialAState, initialState, M]
  · intro index s hindex hs
    apply denoteAInstrs_eq_arun
    exact extended_body_defined c hc index hindex s hs
  · intro index s _ hs
    exact extended_body_wordInv c index s hs
  · intro s _
    rfl

/-- Decode one table cell directly from the producer's output planes. -/
def producedCell (c : Cfg) (s : AState) (X : Nat) : Cell :=
  ⟨LeanCompCert.Ports.Section413Cells.decodeZ (s.arr (tableLo c + X)),
    LeanCompCert.Ports.Section413Cells.decodeZ (s.arr (tableHi c + X))⟩

theorem producer_output_eq_tFlag (c : Cfg) (hc : TableAdmissible c) :
    (rawFinal c).regs rViol = c.tFlag :=
  (LeanCompCert.Ports.Section413G1TableSound.rawFinal_core_tRun c hc).1

/-- A clean producer output identifies every produced cell with the source
G1 recurrence.  The proof is pointwise and symbolic; it does not enumerate
the table. -/
theorem producedCell_eq_source (c : Cfg) (hc : TableAdmissible c)
    (hsound : LeanCompCert.Ports.Section413G1Sound.Admissible c)
    (hzero : (rawFinal c).regs rViol = 0)
    (X : Nat) (hX : 1 ≤ X) (hXc : X ≤ c.cap) :
    producedCell c (rawFinal c) X =
      (LeanCompCert.Ports.Section413G1Sound.g1Prefix
        c.rounds c.checkLo c.cap X).g := by
  have hflag : c.tFlag = 0 :=
    (producer_output_eq_tFlag c hc).symm.trans hzero
  have hraw := LeanCompCert.Ports.Section413G1TableSound.rawFinal_cell
    c hc hsound X hX hXc
  have hrel := LeanCompCert.Ports.Section413G1Sound.sweep_prefix
    c hsound hflag X hXc
  unfold producedCell
  rw [hraw.1, hraw.2]
  exact hrel.g_eq

/-- Soundness direction used by a physical CompCert run admission.  The
premise observes the compiled producer's output register; compiler refinement
recovers the clean symbolic producer state. -/
theorem producer_compiled_zero_sound (c : Cfg) (hc : TableAdmissible c)
    (base : Int) (mem : Verified.MemFragment.Mem)
    (hBase : BaseOk (producerProgram c).arrayLen base)
    (hCells : ∀ k, k < (producerProgram c).arrayLen →
      mem (cellAddr base k) = some (0 : Int))
    (hzero : Option.bind
      (Verified.MemFragment.evalMCCSequence
        ((producerProgram c).initialMCCWithMem base mem)
        (producerProgram c).compile)
      (fun m : Verified.MemFragment.MCCState =>
        m.env ⟨(producerProgram c).output + 1⟩) = some 0) :
    (rawFinal c).regs rViol = 0 := by
  obtain ⟨m, hEval, hRel⟩ :=
    AProgram.evalCC_compile_fromArray
      (producerProgram c) (producerProgram_wf c) base hBase
      (fun _ => 0) mem hCells (fun _ _ => by decide)
      (rawFinal c) (producer_runFromZero c hc)
  rw [hEval] at hzero
  have hmachine : m.env ⟨rViol + 1⟩ = some (0 : Int) := by
    simpa only [producerProgram, Option.bind_some] using hzero
  have hrViol : rViol < (producerProgram c).regCount := by
    simp [producerProgram, rViol,
      LeanCompCert.Ports.Section413G1TableProgram.regCount]
  have hsource := hRel.hregs.1 rViol hrViol
  rw [hmachine] at hsource
  have hcast : (((rawFinal c).regs rViol : Nat) : Int) = 0 :=
    Option.some.inj hsource.symm
  exact_mod_cast hcast

#print axioms producerProgram_wf
#print axioms producer_runFromZero
#print axioms producedCell_eq_source
#print axioms producer_compiled_zero_sound

end LeanCompCert.Ports.Section413G1TableProducer

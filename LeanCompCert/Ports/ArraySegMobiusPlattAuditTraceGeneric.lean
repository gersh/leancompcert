import LeanCompCert.Ports.ArraySegMobiusPlattAuditCertificate
import LeanCompCert.Ports.ArraySegMobiusSquaredFold

/-!
# Generic trace projection for audited squared programs

This module contains only universally quantified trace algebra.  It is kept
separate from the enormous closed Platt configurations so Lean never reduces
a closed `List.range` while checking the algebraic proof.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlattAuditTraceGeneric

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusSquaredFold
open LeanCompCert.Ports.MobiusResidueRealisation

/-- The result-store suffix copies the live violation counter to the program
output and never subsequently changes that output register. -/
theorem mobiusLiveEpilogue_output (c : Cfg) (s : AState) :
    (arun 0 s (mobiusLiveEpilogue c)).regs outputReg = s.regs rMViol := by
  simp [mobiusLiveEpilogue, storeResult, arun, astep, AState.writeReg,
    AState.writeArr_regs, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, outputReg,
    rTLo, rTHi, rCeil, rCeilSq, rMViol]

/-- The result-store epilogue preserves the low accumulator limb. -/
theorem mobiusLiveEpilogue_tLo (c : Cfg) (s : AState) :
    (arun 0 s (mobiusLiveEpilogue c)).regs rTLo = s.regs rTLo := by
  simp [mobiusLiveEpilogue, storeResult, arun, astep, AState.writeReg,
    AState.writeArr_regs, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, outputReg,
    rTLo, rTHi, rCeil, rCeilSq, rMViol]

/-- The result-store epilogue preserves the high accumulator limb. -/
theorem mobiusLiveEpilogue_tHi (c : Cfg) (s : AState) :
    (arun 0 s (mobiusLiveEpilogue c)).regs rTHi = s.regs rTHi := by
  simp [mobiusLiveEpilogue, storeResult, arun, astep, AState.writeReg,
    AState.writeArr_regs, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, outputReg,
    rTLo, rTHi, rCeil, rCeilSq, rMViol]

/-- Convert the total-state result of any squared program to its indexed
transparent residue projection. -/
theorem squaredProgram_total_output_to_indexed_viol_zero
    (c : Cfg) (k : Nat) (seed : MobLiveSeed)
    (h :
      let p := mobiusLiveSquaredProgram c k seed
      let sEntry := arun 0 initialAState p.init
      let sLoop := (List.range p.loopCount).foldl
        (fun s idx => arun idx s p.body) sEntry
      let sFinal := arun 0 sLoop p.epilogue
      sFinal.regs p.output = 0) :
    let fuel := c.period * (c.rootCount + c.segCount)
    (squaredCombinedIndexedRun 0 c k fuel
      (combinedEntry c seed)).regs rMViol = 0 := by
  change
    (arun 0
      ((List.range (c.period * (c.rootCount + c.segCount))).foldl
        (fun s idx => arun idx s
          (c.coreBody ++ mobiusLiveSquaredResidue k))
        (combinedEntry c seed))
      (mobiusLiveEpilogue c)).regs outputReg = 0 at h
  rw [foldl_range_squaredCombined_eq_indexedRun_zero] at h
  rw [mobiusLiveEpilogue_output] at h
  exact h

/-- Version whose hypothesis retains an opaque computation record.  This
avoids asking the elaborator to unfold a closed Platt computation merely to
match the already-compiled total-state receipt. -/
theorem squaredComputation_total_output_to_indexed_viol_zero
    (comp : AComputation) (c : Cfg) (k : Nat) (seed : MobLiveSeed)
    (hprogram : comp.program = mobiusLiveSquaredProgram c k seed)
    (h :
      let sEntry := arun 0 initialAState comp.program.init
      let sLoop := (List.range comp.program.loopCount).foldl
        (fun s idx => arun idx s comp.program.body) sEntry
      let sFinal := arun 0 sLoop comp.program.epilogue
      sFinal.regs comp.program.output = 0) :
    let fuel := c.period * (c.rootCount + c.segCount)
    (squaredCombinedIndexedRun 0 c k fuel
      (combinedEntry c seed)).regs rMViol = 0 := by
  rw [hprogram] at h
  exact squaredProgram_total_output_to_indexed_viol_zero c k seed h

/-- Transport an observed low carry from an opaque computation state to the
pre-epilogue indexed squared trace. -/
theorem squaredComputation_total_tLo_to_indexed
    (comp : AComputation) (c : Cfg) (k : Nat) (seed : MobLiveSeed)
    (hprogram : comp.program = mobiusLiveSquaredProgram c k seed)
    (value : Nat)
    (h :
      let sEntry := arun 0 initialAState comp.program.init
      let sLoop := (List.range comp.program.loopCount).foldl
        (fun s idx => arun idx s comp.program.body) sEntry
      let sFinal := arun 0 sLoop comp.program.epilogue
      sFinal.regs rTLo = value) :
    let fuel := c.period * (c.rootCount + c.segCount)
    (squaredCombinedIndexedRun 0 c k fuel
      (combinedEntry c seed)).regs rTLo = value := by
  rw [hprogram] at h
  change
    (arun 0
      ((List.range (c.period * (c.rootCount + c.segCount))).foldl
        (fun s idx => arun idx s
          (c.coreBody ++ mobiusLiveSquaredResidue k))
        (combinedEntry c seed))
      (mobiusLiveEpilogue c)).regs rTLo = value at h
  rw [foldl_range_squaredCombined_eq_indexedRun_zero] at h
  rw [mobiusLiveEpilogue_tLo] at h
  exact h

/-- High-limb form of the same opaque carry transport. -/
theorem squaredComputation_total_tHi_to_indexed
    (comp : AComputation) (c : Cfg) (k : Nat) (seed : MobLiveSeed)
    (hprogram : comp.program = mobiusLiveSquaredProgram c k seed)
    (value : Nat)
    (h :
      let sEntry := arun 0 initialAState comp.program.init
      let sLoop := (List.range comp.program.loopCount).foldl
        (fun s idx => arun idx s comp.program.body) sEntry
      let sFinal := arun 0 sLoop comp.program.epilogue
      sFinal.regs rTHi = value) :
    let fuel := c.period * (c.rootCount + c.segCount)
    (squaredCombinedIndexedRun 0 c k fuel
      (combinedEntry c seed)).regs rTHi = value := by
  rw [hprogram] at h
  change
    (arun 0
      ((List.range (c.period * (c.rootCount + c.segCount))).foldl
        (fun s idx => arun idx s
          (c.coreBody ++ mobiusLiveSquaredResidue k))
        (combinedEntry c seed))
      (mobiusLiveEpilogue c)).regs rTHi = value at h
  rw [foldl_range_squaredCombined_eq_indexedRun_zero] at h
  rw [mobiusLiveEpilogue_tHi] at h
  exact h

end LeanCompCert.Ports.ArraySegMobiusPlattAuditTraceGeneric

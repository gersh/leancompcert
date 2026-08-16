import LeanCompCert.Ports.R2SegWindowPosition
import LeanCompCert.Ports.R2SegMarkingInit
import LeanCompCert.Ports.R2RuntimeProductionAuditReceipt

/-!
# Exact production-window coverage for the compiled `R₂*` sweep

The retained production receipt already yields a successful source execution
through the fail-safe compiler audit.  This module proves that the source
execution traverses the literal flattened schedule for all `21,000` windows,
resets the round cursor at the end, and advances the window base to the first
integer after the paper range.  No loop is evaluated by Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.PsiSegSieve (seedRegs)

set_option maxRecDepth 4096

/-- Every compact runtime initializer starts at its configured first window. -/
theorem runtimeEntry_position (c : R2Cfg) (seed : R2Seed)
    (arr : Nat → Nat) (hloM : c.lo < M) :
    let entry := arun 0 (initialAStateWithArray arr)
      (r2RuntimeProgram c seed).init
    entry.regs rR = 0 ∧ entry.regs rW = c.lo := by
  let start := initialAStateWithArray arr
  have hstart : start.regs rR = 0 := rfl
  have hseed := seedList_mark_position_run c seed start hstart hloM
  simpa only [r2RuntimeProgram, start] using hseed

/-- The entire flattened runtime loop covers exactly the configured windows.
This stays generic in `c`, preventing the kernel from expanding a concrete
production body while checking the proof. -/
theorem runtimeLoop_position (c : R2Cfg) (seed : R2Seed)
    (arr : Nat → Nat) (hloM : c.lo < M)
    (hperiod0 : 0 < c.period) (hperiodM : c.period < M)
    (hspan : c.lo + c.segCount * c.segLen < M) :
    let entry := arun 0 (initialAStateWithArray arr)
      (r2RuntimeProgram c seed).init
    let loopOut := (List.range (c.period * c.segCount)).foldl
      (fun s index => arun index s c.body) entry
    loopOut.regs rR = 0 ∧
      loopOut.regs rW = c.lo + c.segCount * c.segLen := by
  let entry := arun 0 (initialAStateWithArray arr)
    (r2RuntimeProgram c seed).init
  have hentry := runtimeEntry_position c seed arr hloM
  change entry.regs rR = 0 ∧ entry.regs rW = c.lo at hentry
  have hprefix := bodyWindowPrefix_position c c.segCount entry c.lo
    hentry.1 hentry.2 hperiod0 hperiodM hspan
  rw [bodyWindowPrefix_eq_range] at hprefix
  simpa only [entry] using hprefix

/-- Any successful source execution of the production program has traversed
the full configured range.  The epilogue frames both position registers. -/
theorem runtimeSource_position (c : R2Cfg) (seed : R2Seed)
    (arr : Nat → Nat) (out : AState)
    (hloM : c.lo < M) (hperiod0 : 0 < c.period)
    (hperiodM : c.period < M)
    (hspan : c.lo + c.segCount * c.segLen < M)
    (hRun :
      (r2RuntimeProgram c seed).runFromArray arr = some out) :
    out.regs rR = 0 ∧
      out.regs rW = c.lo + c.segCount * c.segLen := by
  let p := r2RuntimeProgram c seed
  let entry := arun 0 (initialAStateWithArray arr) p.init
  let loopOut := (List.range (c.period * c.segCount)).foldl
    (fun s index => arun index s c.body) entry
  have hloop := runtimeLoop_position c seed arr hloM hperiod0 hperiodM hspan
  change loopOut.regs rR = 0 ∧
    loopOut.regs rW = c.lo + c.segCount * c.segLen at hloop
  have hout := AProgram.eq_arun_of_runFromArray_eq_some p arr out hRun
  change out = arun 0 loopOut c.epilogue at hout
  have hframeR :
      (arun 0 loopOut c.epilogue).regs rR =
        loopOut.regs rR :=
    arun_frame 0 rR c.epilogue (by rfl) loopOut
  have hframeW :
      (arun 0 loopOut c.epilogue).regs rW =
        loopOut.regs rW :=
    arun_frame 0 rW c.epilogue (by rfl) loopOut
  rw [hout]
  exact ⟨hframeR.trans hloop.1, hframeW.trans hloop.2⟩

/-- The two retained CompCert executions therefore certify exact range
coverage in addition to their zero verdict and terminal accumulator words. -/
theorem runtimeProduction_verified_position :
    ∃ packed out : AState,
      (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).runFromArray
          packed.arr = some out ∧
        out.regs rR = 0 ∧
          out.regs rW = runtimeProductionCfg.lo +
            runtimeProductionCfg.segCount * runtimeProductionCfg.segLen := by
  rcases runtimeProduction_verified_source_observation with
    ⟨packed, out, hRun, _hpacked, _hreceipt, _hobs⟩
  exact ⟨packed, out, hRun,
    runtimeSource_position runtimeProductionCfg runtimeProductionSeed
      packed.arr out (by decide) (by decide) (by decide) (by decide) hRun⟩

#print axioms runtimeEntry_position
#print axioms runtimeLoop_position
#print axioms runtimeSource_position
#print axioms runtimeProduction_verified_position

end LeanCompCert.Ports.R2SegSieve

import LeanCompCert.Ports.Prop1224CellGuardedSemantics

/-!
# Source projection of the Proposition 12.2.4 accumulator guard

An accepting signed guarded computation proves a no-decrease fact for every
literal source-body invocation.  This is the causal fact consumed by the
modulo-first accumulation telescope; the production prefix remains a symbolic
fold throughout the proof.
-/

namespace LeanCompCert.Ports.Prop1224CellGuardedSemantics

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.Prop1224Cell
open LeanCompCert.Ports.Prop1224CellGuarded

/-- Source-only statement extracted from a successful guarded denotation.
Neither the prefix nor the production loop bound is evaluated by Lean. -/
theorem guardedProgram_denote_zero_projected_accumulator
    (c : CellCfg) (seed : CellSeed)
    (hDenote : (guardedProgram c seed).denote = some 0)
    (j : Nat) (hj : j < c.period * c.segCount) :
    let entry := arun 0 initialAState (c.init seed)
    let sourceBefore := (List.range j).foldl
      (fun st idx => arun idx st c.body) entry
    let sourceOut := arun j sourceBefore c.body
    sourceBefore.regs rG ≤ sourceOut.regs rG := by
  let entry := arun 0 initialAState (c.init seed)
  let guardedBefore := (List.range j).foldl
    (fun st idx => arun idx st (guardedBody c)) entry
  let sourceBefore := (List.range j).foldl
    (fun st idx => arun idx st c.body) entry
  let guardedOut := arun j guardedBefore c.body
  let sourceOut := arun j sourceBefore c.body
  have hstep := guardedProgram_denote_zero_step c seed hDenote j hj
  change guardedBefore.regs rVAccWrap = 0 ∧
      guardedBefore.regs rG ≤ guardedOut.regs rG ∧
      guardedBefore.regs rVSumWrap = 0 ∧
      (guardedOut.regs 223 = 1 →
        sourceGuardedPublishedG c guardedBefore guardedOut ≤
          sourceGuardedSumWord c guardedBefore guardedOut) at hstep
  have hagree : SourceAgree sourceRegBound guardedBefore sourceBefore :=
    guardedBodies_sourceAgree c (List.range j) entry entry
      (SourceAgree.refl sourceRegBound entry)
  have houtAgree : SourceAgree sourceRegBound guardedOut sourceOut :=
    arun_sourceAgree hagree c.body (body_wf_source c)
  have hin : guardedBefore.regs rG = sourceBefore.regs rG :=
    hagree.2 rG (by decide)
  have hout : guardedOut.regs rG = sourceOut.regs rG :=
    houtAgree.2 rG (by decide)
  rw [hin, hout] at hstep
  exact hstep.2.1

#print axioms guardedProgram_denote_zero_projected_accumulator

end LeanCompCert.Ports.Prop1224CellGuardedSemantics

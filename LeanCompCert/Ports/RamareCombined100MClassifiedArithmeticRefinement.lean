import LeanCompCert.Ports.RamareCombined100MClassRefinement
import LeanCompCert.Ports.RamareCombined100MLambdaPsiSweep

/-!
# Source refinement through the Ramaré candidate arithmetic

This file joins two independently checked seams without reducing their
combined instruction list.  `RamareCombined100MClassRefinement` identifies
the complete seven-plane classifier with the source segmented `finish` and
proves that it clears the consumed cell.  `RamareCombined100MLambdaPsiSweep`
proves the following log, lambda, quotient-sum, and psi blocks from an
explicit arithmetic invariant on that concrete classified state.

The theorem below retains both observations.  It is the per-candidate
induction lemma needed by the finite classification sweep.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ClassifiedArithmeticRefinement

open LeanCompCert.Verified.Reflect (M)
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun)
open LeanCompCert.Ports.RamareCombined100M

set_option maxRecDepth 20000 in
/-- Complete source-facing semantics of one live classified candidate,
through the log/lambda/sum/psi arithmetic suffix.  The only remaining
premise about that suffix is its explicit word/table invariant
`ArithmeticPre`; no property of the classifier is assumed there. -/
theorem ofChain_classifiedArithmeticBody_run
    (lo segLen segCount tableHi k : Nat) (logs : List LogCell)
    (s : AState)
    (hL : 0 < segLen)
    (hrel : ShapeSieve.CellRel
      ((ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).readPlaneCell
        (s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps) s)
      (RamareCombined100MSeg.markCell
        (ShapeSieve.factorRows
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).table)
        (s.regs ShapeSieve.rR -
            (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
          s.regs ShapeSieve.rW)))
    (hn : 0 < s.regs ShapeSieve.rR -
        (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
          s.regs ShapeSieve.rW)
    (hN : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
            s.regs ShapeSieve.rW ≤ 100000000)
    (hzero : s.regs 0 = 0)
    (hmarkPhase : s.regs 10 = 0)
    (hclassPhase : s.regs 11 = 1)
    (hT : (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps ≤
      s.regs ShapeSieve.rR)
    (hR : s.regs ShapeSieve.rR < M)
    (hsum : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        s.regs ShapeSieve.rW < M)
    (h1 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        segLen < M)
    (h2 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        2 * segLen < M)
    (h3 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        3 * segLen < M)
    (h4 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        4 * segLen < M)
    (h5 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        5 * segLen < M)
    (h6 : s.regs ShapeSieve.rR -
          (ShapeSieve.Cfg.ofChain lo segLen segCount tableHi).markSteps +
        6 * segLen < M)
    (hpre :
      let c : LambdaPsiSweep.Cfg :=
        { shape := ShapeSieve.Cfg.ofChain lo segLen segCount tableHi, logs }
      LambdaPsiSweep.ArithmeticPre c k
        (LambdaPsiSweep.afterClassification c k s)) :
    let shape := ShapeSieve.Cfg.ofChain lo segLen segCount tableHi
    let c : LambdaPsiSweep.Cfg := { shape, logs }
    let j := s.regs ShapeSieve.rR - shape.markSteps
    let n := j + s.regs ShapeSieve.rW
    let classified := LambdaPsiSweep.afterClassification c k s
    let out := arun k s (LambdaPsiSweep.classifiedArithmeticBody c)
    ShapeSieve.shapeRegs classified =
        RamareCombined100MSeg.finish n
          (RamareCombined100MSeg.markCell
            (ShapeSieve.factorRows shape.table) n) ∧
      shape.readPlaneCell j classified = ShapeSieve.emptyPlaneCell ∧
      classified.regs 132 = n ∧
      classified.regs 11 = 1 ∧
      out.regs LambdaPsiSweep.lRLogL =
        classified.regs LambdaPsiSweep.lRLogL +
        RS62.incLWord n ∧
      out.regs LambdaPsiSweep.lRLogU =
        classified.regs LambdaPsiSweep.lRLogU +
        RS62.incUWord n ∧
      LambdaPsiSweep.observeCandidate out =
        LambdaPsiSweep.candidateArithmetic c
          (LambdaPsiSweep.afterLogCandidate k classified) ∧
      out.arr = classified.arr := by
  let shape := ShapeSieve.Cfg.ofChain lo segLen segCount tableHi
  let c : LambdaPsiSweep.Cfg := { shape, logs }
  let j := s.regs ShapeSieve.rR - shape.markSteps
  let n := j + s.regs ShapeSieve.rW
  let classified := LambdaPsiSweep.afterClassification c k s
  have hsource := ShapeSieve.ofChain_classBody_run
    lo segLen segCount tableHi k s hL hrel hn hN hzero hmarkPhase
    hclassPhase hT hR hsum h1 h2 h3 h4 h5 h6
  change ShapeSieve.shapeRegs classified =
      RamareCombined100MSeg.finish n
        (RamareCombined100MSeg.markCell
          (ShapeSieve.factorRows shape.table) n) ∧
    shape.readPlaneCell j classified = ShapeSieve.emptyPlaneCell at hsource
  have harith := LambdaPsiSweep.classifiedArithmeticBody_run c k s
    hclassPhase hT hR hsum hpre
  change classified.regs 132 = n ∧
      classified.regs 11 = 1 ∧
      (arun k s (LambdaPsiSweep.classifiedArithmeticBody c)).regs
          LambdaPsiSweep.lRLogL =
        classified.regs LambdaPsiSweep.lRLogL +
          RS62.incLWord (classified.regs 132) ∧
      (arun k s (LambdaPsiSweep.classifiedArithmeticBody c)).regs
          LambdaPsiSweep.lRLogU =
        classified.regs LambdaPsiSweep.lRLogU +
          RS62.incUWord (classified.regs 132) ∧
      LambdaPsiSweep.observeCandidate
          (arun k s (LambdaPsiSweep.classifiedArithmeticBody c)) =
        LambdaPsiSweep.candidateArithmetic c
          (LambdaPsiSweep.afterLogCandidate k classified) ∧
      (arun k s (LambdaPsiSweep.classifiedArithmeticBody c)).arr =
        classified.arr
    at harith
  have hlogL :
      (arun k s (LambdaPsiSweep.classifiedArithmeticBody c)).regs
          LambdaPsiSweep.lRLogL =
        classified.regs LambdaPsiSweep.lRLogL + RS62.incLWord n := by
    simpa [harith.1] using harith.2.2.1
  have hlogU :
      (arun k s (LambdaPsiSweep.classifiedArithmeticBody c)).regs
          LambdaPsiSweep.lRLogU =
        classified.regs LambdaPsiSweep.lRLogU + RS62.incUWord n := by
    simpa [harith.1] using harith.2.2.2.1
  exact ⟨hsource.1, hsource.2, harith.1, harith.2.1,
    hlogL, hlogU, harith.2.2.2.2.1,
    harith.2.2.2.2.2⟩

end LeanCompCert.Ports.RamareCombined100M.ClassifiedArithmeticRefinement

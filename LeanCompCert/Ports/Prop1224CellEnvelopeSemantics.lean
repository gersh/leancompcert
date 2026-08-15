import LeanCompCert.Ports.Prop1224CellEnvelopeNumerator
import LeanCompCert.Ports.Prop1224CellEnvelopeCeilInput
import LeanCompCert.Ports.Prop1224CellEnvelopeDivide
import LeanCompCert.Ports.Prop1224CellEnvelopeRescale

/-!
# Exact semantics of the Proposition 12.2.4 cell envelope

This module proves the natural-number meaning of the literal five-instruction
block immediately before the margin comparison.  It is symbolic in the row
coefficient and cube-root word and executes no campaign cell in Lean.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.Prop1224Margin

/-- Exact emitted envelope word.  The hypotheses are the source positivity
needed by ceiling division and the three fixed-width no-wrap obligations. -/
theorem envelopeBlock_run (c : CellCfg) (index : Nat) (s : AState)
    (t : Nat) (htWord : s.regs rT = t) (ht : 0 < t)
    (hprod : c.afHi * 2 ^ 5 < M)
    (hadd : c.afHi * 2 ^ 5 + t < M)
    (hscaled : envHi c.afHi t * 2 ^ (C - E) < M) :
    let out := arun index s c.envelopeBlock
    out.regs 217 = envHi c.afHi t * 2 ^ (C - E) := by
  dsimp only
  rw [envelopeBlock_eq_lift, arun_lift_regs]
  let s1 := srun index s.regs (envelopeNumeratorScalar c)
  let s2 := srun index s1 (envelopeCeilInputScalar c)
  let s3 := srun index s2 (envelopeDivideScalar c)
  have h1 : s1 213 = c.afHi * 2 ^ 5 :=
    envelopeNumeratorScalar_run c index s.regs hprod
  have h1t : s1 rT = t := by
    have hframe : ∀ i ∈ envelopeNumeratorScalar c, sdest i ≠ rT := by
      simp [envelopeNumeratorScalar, envelopeScalar, rT]
    exact (srun_untouched index rT (envelopeNumeratorScalar c) hframe
      s.regs).trans htWord
  have h2 : s2 215 = c.afHi * 2 ^ 5 + t - 1 :=
    envelopeCeilInputScalar_run c index s1 _ _ h1 h1t ht hadd
  have h2t : s2 rT = t := by
    have hframe : ∀ i ∈ envelopeCeilInputScalar c, sdest i ≠ rT := by
      simp [envelopeCeilInputScalar, envelopeScalar, rT]
    exact (srun_untouched index rT (envelopeCeilInputScalar c) hframe
      s1).trans h1t
  have hsubLt : c.afHi * 2 ^ 5 + t - 1 < M := by omega
  have h3 : s3 216 = (c.afHi * 2 ^ 5 + t - 1) / t :=
    envelopeDivideScalar_run c index s2 _ _ h2 h2t ht hsubLt
  have hceil : (c.afHi * 2 ^ 5 + t - 1) / t = envHi c.afHi t := by
    rfl
  rw [envelopeScalar_eq_stages, srun_append, srun_append, srun_append]
  exact envelopeRescaleScalar_run c index s3 _ (h3.trans hceil) hscaled

theorem envelopeBlock_arr_frame (c : CellCfg) (index : Nat) (s : AState) :
    (arun index s c.envelopeBlock).arr = s.arr := by
  rw [envelopeBlock_eq_lift, arun_lift_arr]

#print axioms envelopeBlock_run
#print axioms envelopeBlock_arr_frame

end LeanCompCert.Ports.Prop1224Cell

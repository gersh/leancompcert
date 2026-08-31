import LeanCompCert.Ports.RamareCombined100MShapeHostAdvanceGuards

/-!
# Classification-phase advance premise at the terminal cursor

Once marking has exhausted the production prime table, classification rounds
retain the explicit terminal cursor.  This lemma packages just the word and
nonzero facts needed by the emitted advance block while its phase bit is zero.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem advanceWordPre_of_classCursor
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (s : AState) (table : Nat → Nat)
    (hphase : s.regs 10 = 0) (hpast : s.regs 25 = 1)
    (hpi : s.regs rPi = c.tableLen)
    (hpow : s.regs rPow = 1) (hbase : s.regs rBase = 1)
    (htable : ∀ pi, pi ≤ c.tableLen →
      s.arr (pi + c.tableBase) = table pi)
    (hhi : c.hi < M) (hK : c.tableLen < M)
    (haddr : c.tableLen + c.tableBase < M)
    (hjpow : s.regs rJ + 1 < M) (hseg : c.segLen + 1 < M)
    (hstepsPos : 0 < c.markSteps) (hsteps : c.markSteps < M)
    (hround : c.markSteps ≤ s.regs rR)
    (hviol : s.regs rViol < M) (hvmark : s.regs rVMark < M) :
    AdvanceWordPre c s table := by
  have hroundNe : s.regs rR ≠ c.markSteps - 1 := by omega
  refine {
    table := htable
    values := ?_
    pow_ne_zero := ?_
    seg_sentinel := hseg
    mark_steps := hsteps
    viol := ?_
    vmark := ?_ }
  · refine {
      h10 := by rw [hphase]; omega
      h25 := by rw [hpast]; omega
      hmul := by rw [hpow, hbase]; exact one_lt_M
      hhi := hhi
      hsum := ?_
      hK := hK
      haddr := ?_
      hactive := ?_
      hbump := ?_
      hstep := ?_
      hmodes := ?_
      hjpow := ?_
      hpowOut := ?_
      hbaseOut := ?_ }
    · rw [hphase, hpast, hpi, hpow, hbase]
      simpa [Cfg.stepPrime, Cfg.bumpPower, advanceActive] using hK
    · rw [hphase, hpast, hpi, hpow, hbase]
      simpa [Cfg.stepPrime, Cfg.bumpPower, advanceActive, clampPi] using haddr
    · simp [hphase, advanceActive]
    · simp [hphase, Cfg.bumpPower, advanceActive]
    · simp [hphase, Cfg.stepPrime, Cfg.bumpPower, advanceActive]
    · simp [hphase, Cfg.stepPrime, Cfg.bumpPower, advanceActive]
    · rw [hpow]
      exact hjpow
    · rw [hphase, hpast, hpi, hpow, hbase]
      simp [Cfg.stepPrime, Cfg.bumpPower, advanceActive, clampPi,
        nextPowValue, one_lt_M]
    · rw [hphase, hpast, hpi, hpow, hbase]
      simp [Cfg.stepPrime, Cfg.bumpPower, advanceActive, clampPi,
        nextBaseValue, one_lt_M]
  · rw [hphase, hpast, hpi, hpow, hbase]
    simp [Cfg.stepPrime, Cfg.bumpPower, advanceActive, clampPi,
      nextPowValue]
  · rw [hphase, hpast, hpi, hpow, hbase]
    simpa [Cfg.stepPrime, Cfg.bumpPower, advanceActive, clampPi,
      Cfg.budgetFailure, eqBit, hroundNe] using hviol
  · rw [hphase, hpast, hpi, hpow, hbase]
    simpa [Cfg.stepPrime, Cfg.bumpPower, advanceActive, clampPi,
      Cfg.budgetFailure, eqBit, hroundNe] using hvmark

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

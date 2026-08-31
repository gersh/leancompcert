import LeanCompCert.Ports.RamareCombined100MShapeHostClassAdvancePre

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem classAdvance_j
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (k : Nat) (s : AState) (table : Nat → Nat)
    (hpre : AdvanceWordPre c s table)
    (h10 : s.regs 10 = 0) (h25 : s.regs 25 = 1)
    (hpi : s.regs rPi = c.tableLen)
    (hpow : s.regs rPow = 1) (hbase : s.regs rBase = 1)
    (j : Nat) (hj : s.regs rJ = j) :
    (arun k s c.markAdvanceBody).regs rJ = j + 1 := by
  have ha := c.markAdvanceBody_run k s hpre.values hpre.pow_ne_zero
    hpre.seg_sentinel hpre.mark_steps hpre.viol hpre.vmark
  dsimp only at ha
  rw [ha.2.2.2.1, h10, h25, hpi, hpow, hbase, hj]
  simp [Cfg.stepPrime, Cfg.bumpPower, advanceActive, clampPi,
    nextPowValue, Cfg.selectedOffset, nextOffset]

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

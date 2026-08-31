import LeanCompCert.Ports.RamareCombined100MShapeHostClassAdvancePre

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem classAdvance_pow
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (k : Nat) (s : AState) (table : Nat → Nat)
    (hpre : AdvanceWordPre c s table)
    (h10 : s.regs 10 = 0) (h25 : s.regs 25 = 1)
    (hpow : s.regs rPow = 1) (hbase : s.regs rBase = 1) :
    (arun k s c.markAdvanceBody).regs rPow = 1 := by
  have ha := c.markAdvanceBody_run k s hpre.values hpre.pow_ne_zero
    hpre.seg_sentinel hpre.mark_steps hpre.viol hpre.vmark
  dsimp only at ha
  rw [ha.2.1, h10, h25, hpow, hbase]
  simp [Cfg.stepPrime, Cfg.bumpPower, advanceActive, nextPowValue]

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

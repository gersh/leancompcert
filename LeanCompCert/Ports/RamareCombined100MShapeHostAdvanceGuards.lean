import LeanCompCert.Ports.RamareCombined100MShapeHostTotality

/-!
# Split cursor-table guards for shape-host totality

These two lemmas project only the load address and nonzero divisor needed by
partial semantics from the existing symbolic `AdvanceWordPre` record.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

theorem tableAddress_lt_of_advanceWordPre
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (len k : Nat) (s : AState) (table : Nat → Nat)
    (hpre : AdvanceWordPre c s table)
    (halloc : c.tableLen + c.tableBase < len) :
    let selected := arun k s c.markAdvanceSelectBody
    (arun k selected (markAdvanceLoadPrefix c)).regs 95 < len := by
  let selected := arun k s c.markAdvanceSelectBody
  have hs := c.markAdvanceSelectBody_run k s hpre.values.h10
    hpre.values.h25 hpre.values.hmul hpre.values.hhi
    hpre.values.hsum hpre.values.hK
  dsimp only at hs
  have hpi : selected.regs rPi = clampPi c.tableLen
      (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
        (s.regs rPow) (s.regs rBase)) := hs.2.2.2.2.1
  have haddrM : selected.regs rPi + c.tableBase < M := by
    rw [hpi]
    exact hpre.values.haddr
  have haddrLen : selected.regs rPi + c.tableBase < len := by
    rw [hpi]
    exact Nat.lt_of_le_of_lt
      (Nat.add_le_add_right (clampPi_le _ _) c.tableBase) halloc
  dsimp only [selected] at haddrM haddrLen ⊢
  simpa [markAdvanceLoadPrefix, arun, astep, AState.writeReg,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    Nat.mod_eq_of_lt haddrM] using haddrLen

theorem nextPower_ne_of_advanceWordPre
    (c : LeanCompCert.Ports.RamareCombined100M.ShapeSieve.Cfg)
    (k : Nat) (s : AState) (table : Nat → Nat)
    (hpre : AdvanceWordPre c s table) :
    let selected := arun k s c.markAdvanceSelectBody
    let loaded := arun k selected c.markAdvanceLoadBody
    let valued := arun k loaded Cfg.markAdvanceValueBody
    valued.regs rPow ≠ 0 := by
  have hv := c.markAdvanceSelectLoadValueBody_run k s
    hpre.values.h10 hpre.values.h25 hpre.values.hmul hpre.values.hhi
    hpre.values.hsum hpre.values.hK hpre.values.haddr
    hpre.values.hactive hpre.values.hbump hpre.values.hstep
    hpre.values.hmodes hpre.values.hjpow hpre.values.hpowOut
    hpre.values.hbaseOut
  dsimp only at hv
  have hp :
      (arun k (arun k (arun k s c.markAdvanceSelectBody)
        c.markAdvanceLoadBody) Cfg.markAdvanceValueBody).regs rPow =
        nextPowValue (advanceActive (s.regs 10) (s.regs 25))
          (c.bumpPower (s.regs 10) (s.regs 25)
            (s.regs rPow) (s.regs rBase))
          (c.stepPrime (s.regs 10) (s.regs 25)
            (s.regs rPow) (s.regs rBase))
          (s.regs rPow) (s.regs rPow * s.regs rBase)
          (s.arr (clampPi c.tableLen
            (s.regs rPi + c.stepPrime (s.regs 10) (s.regs 25)
              (s.regs rPow) (s.regs rBase)) + c.tableBase)) := by
    simpa only [arun_append] using hv.2.2.2.2.2.2.1
  dsimp only
  rw [hp]
  exact hpre.pow_ne_zero

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

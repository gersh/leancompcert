import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassCursorPi
import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassCursorPow
import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassCursorBase
import LeanCompCert.Ports.RamareCombined100MShapeHostProductionClassCursorJ

/-!
# Split production classification cursor invariant

The four cursor coordinates are proved by independent modules above.  This
file only frames them through the classifier/tail/arithmetic suffix and joins
their opaque results into a reusable invariant.
-/

namespace LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100M.ShapeSieve

set_option maxRecDepth 10000 in
theorem productionBody_afterMark_frame
    (logs : List LogCell) (k : Nat) (s : AState) (r : Nat)
    (hc : writes r productionCursorCfg.classBody = false)
    (ht : writes r productionCursorCfg.tailBody = false)
    (ha : writes r (LambdaPsiSweep.arithmeticBody
      ({ shape := productionCursorCfg, logs } : LambdaPsiSweep.Cfg)) = false) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    (arun k s (LambdaPsiSweep.body c)).regs r =
      (arun k s productionCursorCfg.markBody).regs r := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  let marked := arun k s productionCursorCfg.markBody
  let classified := arun k marked productionCursorCfg.classBody
  let tailed := arun k classified productionCursorCfg.tailBody
  have hcF : classified.regs r = marked.regs r :=
    arun_frame k r productionCursorCfg.classBody hc marked
  have htF : tailed.regs r = classified.regs r :=
    arun_frame k r productionCursorCfg.tailBody ht classified
  have haF : (arun k tailed (LambdaPsiSweep.arithmeticBody c)).regs r =
      tailed.regs r := arun_frame k r _ ha tailed
  dsimp only
  rw [BodyRefinement.body_eq_mark_class_tail_arithmetic c]
  simp only [arun_append]
  exact haF.trans (htF.trans hcF)

structure ProductionClassCursorInv (fuel : Nat) (s : AState) : Prop where
  pi_eq : s.regs rPi = productionCursorCfg.tableLen
  pow_eq : s.regs rPow = 1
  base_eq : s.regs rBase = 1
  j_eq : s.regs rJ = productionCursorCfg.segLen + 1 + fuel

theorem ProductionClassCursorInv.machineCursor
    {fuel : Nat} {s : AState} (h : ProductionClassCursorInv fuel s) :
    machinePowerCursor s = productionClassCursor fuel := by
  apply PowerCursor.ext
  · exact h.pi_eq
  · exact h.pow_eq
  · exact h.base_eq
  · exact h.j_eq

theorem ProductionClassCursorInv.pi_le
    {fuel : Nat} {s : AState} (h : ProductionClassCursorInv fuel s) :
    s.regs rPi ≤ productionCursorCfg.tableLen := by
  rw [h.pi_eq]
  exact Nat.le_refl _

theorem ProductionClassCursorInv.pow_ne
    {fuel : Nat} {s : AState} (h : ProductionClassCursorInv fuel s) :
    s.regs rPow ≠ 0 := by rw [h.pow_eq]; decide

theorem ProductionClassCursorInv.start
    (s : AState) (h : machinePowerCursor s = productionTerminalCursor) :
    ProductionClassCursorInv 0 s := by
  refine ⟨congrArg PowerCursor.pi h, congrArg PowerCursor.pow h,
    congrArg PowerCursor.base h, ?_⟩
  have hj := congrArg PowerCursor.j h
  change s.regs rJ = productionCursorCfg.segLen + 1 at hj
  simpa [productionTerminalCursor, productionClassCursor] using hj

set_option maxRecDepth 10000 in
theorem ProductionClassCursorInv.step
    {fuel : Nat} {s : AState} (h : ProductionClassCursorInv fuel s)
    (logs : List LogCell) (k : Nat)
    (hfuel : fuel < productionCursorCfg.segLen)
    (hclass : productionCursorCfg.markSteps ≤ s.regs rR)
    (hviol : s.regs rViol < M) (hvmark : s.regs rVMark < M) :
    let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
    ProductionClassCursorInv (fuel + 1)
      (arun k s (LambdaPsiSweep.body c)) := by
  let c : LambdaPsiSweep.Cfg := { shape := productionCursorCfg, logs }
  have hPi := productionClassMarkBody_pi fuel k s hfuel hclass
    h.machineCursor hviol hvmark
  have hPow := productionClassMarkBody_pow fuel k s hfuel hclass
    h.machineCursor hviol hvmark
  have hBase := productionClassMarkBody_base fuel k s hfuel hclass
    h.machineCursor hviol hvmark
  have hJ := productionClassMarkBody_j fuel k s hfuel hclass
    h.machineCursor hviol hvmark
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (productionBody_afterMark_frame logs k s rPi
      (by rfl) (by rfl) (by rfl)).trans hPi
  · exact (productionBody_afterMark_frame logs k s rPow
      (by rfl) (by rfl) (by rfl)).trans hPow
  · exact (productionBody_afterMark_frame logs k s rBase
      (by rfl) (by rfl) (by rfl)).trans hBase
  · exact (productionBody_afterMark_frame logs k s rJ
      (by rfl) (by rfl) (by rfl)).trans hJ

end LeanCompCert.Ports.RamareCombined100M.SeamBlock.ShapeHost

import LeanCompCert.Ports.Section413WindowBodyReferenceSound
import LeanCompCert.Ports.Section413WindowScannerFoldSound

/-!
# One compiled scanner step refines one paper slot

The core theorem keeps the scheduled, event, and checked states opaque.  This
prevents definitional equality from unfolding the fixed row-check program;
array preservation is discharged structurally by `ScalarOnly`.
-/

namespace LeanCompCert.Ports.Section413WindowScannerReferenceStep
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Section413Cells
open LeanCompCert.Ports.Section413WindowEventScanner
open LeanCompCert.Ports.Section413WindowPipelineSound
open LeanCompCert.Ports.Section413WindowTableReferenceBridge
open LeanCompCert.Ports.Section413WindowBodyReferenceSound
open LeanCompCert.Ports.Section413WindowSchedule

set_option maxRecDepth 100000 in
theorem g1_scanner_step_core (k : Nat) (s p e t : AState)
    (hk : k < productionRows * slots)
    (hword : ∀ j, p.regs j < M) (harray : ∀ j, p.arr j < M)
    (hsched :
      p.regs rN = (slotAt k).n ∧ p.regs rS = (slotAt k).s ∧
      p.regs rQ = (slotAt k).q ∧ p.regs rActive = (slotAt k).active ∧
      p.regs rPair = (slotAt k).pair ∧ p.regs rHalfQ = (slotAt k).halfQ ∧
      p.regs rHalfActive = (slotAt k).halfActive ∧
      p.regs rHalfPair = (slotAt k).halfPair)
    (harr : p.arr =
      (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr)
    (hflag : g1TableCfg.tFlag = 0)
    (hadd : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hr : EventBodyReceipts k p g1Cfg)
    (he : e = arun k p (eventBody g1Cfg))
    (ht : t = arun k e (LeanCompCert.Ports.Section413WindowRowCheck.body
      g1Cfg.checkLo g1Cfg.offset))
    (htadd : t.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hk1lo : p.regs rK1Lo = s.regs rK1Lo)
    (hk1hi : p.regs rK1Hi = s.regs rK1Hi)
    (hk2lo : p.regs rK2Lo = s.regs rK2Lo)
    (hk2hi : p.regs rK2Hi = s.regs rK2Hi)
    (hparr : p.arr = s.arr) :
    Accumulates s t
      (LeanCompCert.Ports.Section413WindowPairingBridge.k1SlotDelta
        g1G 1 (slotAt k).n (k % slots)).lo
      (LeanCompCert.Ports.Section413WindowPairingBridge.k1SlotDelta
        g1G 1 (slotAt k).n (k % slots)).hi
      (LeanCompCert.Ports.Section413WindowPairingBridge.k2SlotDelta
        g1G 1 (slotAt k).n (k % slots)).lo
      (LeanCompCert.Ports.Section413WindowPairingBridge.k2SlotDelta
        g1G 1 (slotAt k).n (k % slots)).hi := by
  have hev := g1_body_slot k p hk hword harray hsched harr hflag hadd hr
  rw [← he] at hev
  have rowFrame (r : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes r
        (LeanCompCert.Ports.Section413WindowRowCheck.body g1Cfg.checkLo
          g1Cfg.offset) = false) : t.regs r = e.regs r := by
    rw [ht]
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k r _ hw e
  have htarr : t.arr = e.arr := by
    rw [ht]
    exact LeanCompCert.Verified.ArrayScalarBlock.arun_scalarOnly_arr k _ e
      (by trivial)
  have htscale : t.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0 := by
    rw [ht, LeanCompCert.Ports.Section413WindowRowCheck.body_scale_frame,
      hev.scale_clean]
  apply Accumulates.of_outputs
  refine ⟨?_, ?_, ?_, ?_, htscale, htadd, ?_⟩
  · rw [rowFrame rK1Lo (by decide), hev.k1Lo_eq, hk1lo]
  · rw [rowFrame rK1Hi (by decide), hev.k1Hi_eq, hk1hi]
  · rw [rowFrame rK2Lo (by decide), hev.k2Lo_eq, hk2lo]
  · rw [rowFrame rK2Hi (by decide), hev.k2Hi_eq, hk2hi]
  · exact htarr.trans (hev.array_eq.trans hparr)

set_option maxRecDepth 100000 in
theorem g1_scanner_step (k : Nat) (s : AState)
    (hk : k < productionRows * slots)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (harr : s.arr =
      (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr)
    (hflag : g1TableCfg.tFlag = 0)
    (hpadd : (scheduledState k s).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (htadd : (checkedState k s g1Cfg).regs
      LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hr : EventBodyReceipts k (scheduledState k s) g1Cfg) :
    Accumulates s (checkedState k s g1Cfg)
      (LeanCompCert.Ports.Section413WindowPairingBridge.k1SlotDelta
        g1G 1 (slotAt k).n (k % slots)).lo
      (LeanCompCert.Ports.Section413WindowPairingBridge.k1SlotDelta
        g1G 1 (slotAt k).n (k % slots)).hi
      (LeanCompCert.Ports.Section413WindowPairingBridge.k2SlotDelta
        g1G 1 (slotAt k).n (k % slots)).lo
      (LeanCompCert.Ports.Section413WindowPairingBridge.k2SlotDelta
        g1G 1 (slotAt k).n (k % slots)).hi := by
  let p := scheduledState k s
  let e := eventedState k s g1Cfg
  let t := checkedState k s g1Cfg
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hsched := LeanCompCert.Ports.Section413WindowSchedule.body_outputs k s hk
  have hparr : p.arr =
      (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr := by
    exact (LeanCompCert.Verified.ArrayScalarBlock.arun_lift_arr k _ s).trans harr
  have schedFrame (r : Nat)
      (hw : LeanCompCert.Verified.ArrayRegFrame.writes r
        LeanCompCert.Ports.Section413WindowSchedule.body = false) :
      p.regs r = s.regs r := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k r _ hw s
  exact g1_scanner_step_core k s p e t hk hpword hparray hsched hparr hflag
    hpadd hr rfl rfl
    htadd (schedFrame rK1Lo (by decide)) (schedFrame rK1Hi (by decide))
    (schedFrame rK2Lo (by decide)) (schedFrame rK2Hi (by decide))
    (LeanCompCert.Verified.ArrayScalarBlock.arun_lift_arr k _ s)

#print axioms g1_scanner_step_core
#print axioms g1_scanner_step

end LeanCompCert.Ports.Section413WindowScannerReferenceStep

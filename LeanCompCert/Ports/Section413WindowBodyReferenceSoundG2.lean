import LeanCompCert.Ports.Section413WindowTableReferenceBridge
import LeanCompCert.Ports.Section413WindowSlotContributionBridge

/-!
# Compiled Section 4.1.3 G2 event body refines one reference slot

This module consumes constant-size event receipts and proves that one
symbolic scanner iteration adds exactly the paper's `k1SlotDelta` and
`k2SlotDelta`.  It never evaluates a production row or table.
-/

namespace LeanCompCert.Ports.Section413WindowBodyReferenceSoundG2

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413Cells
open LeanCompCert.Ports.Section413WindowEventScanner
open LeanCompCert.Ports.Section413WindowPipelineSound
open LeanCompCert.Ports.Section413WindowTableReferenceBridge
open LeanCompCert.Ports.Section413WindowSlotContributionBridge
open LeanCompCert.Ports.Section413WindowSchedule

set_option maxRecDepth 100000 in
theorem g2_first (k : Nat) (p : AState)
    (hk : k < productionRows * slots)
    (hword : ∀ j, p.regs j < M) (harray : ∀ j, p.arr j < M)
    (hs : p.regs rS = (slotAt k).s)
    (hq : p.regs rQ = (slotAt k).q)
    (ha : p.regs rActive = (slotAt k).active)
    (harr : p.arr =
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr)
    (hflag : g2TableCfg.tFlag = 0)
    (hadd : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hr : EventReceipts k p g2Cfg rActive rS rQ rQ true false) :
    Accumulates p (afterFirst k p g2Cfg)
      (eventK1Contribution
        (divisorGate 2 (slotAt k).active (slotAt k).s)
        (referenceDiff g2G (slotAt k).q)
        (safeDen (slotAt k).s) true).lo
      (eventK1Contribution
        (divisorGate 2 (slotAt k).active (slotAt k).s)
        (referenceDiff g2G (slotAt k).q)
        (safeDen (slotAt k).s) true).hi
      (eventK2Contribution
        (divisorGate 2 (slotAt k).active (slotAt k).s)
        (referenceDiff g2G (slotAt k).q) (slotAt k).q false).lo
      (eventK2Contribution
        (divisorGate 2 (slotAt k).active (slotAt k).s)
        (referenceDiff g2G (slotAt k).q) (slotAt k).q false).hi := by
  have hn : (slotAt k).n ≤ productionRows := by
    simp only [slotAt, productionRows, slots] at hk ⊢
    omega
  have hqN : (slotAt k).q ≤ (slotAt k).n := by
    simp only [slotAt]
    exact Nat.div_le_self _ _
  have hqCap : (slotAt k).q ≤ g2TableCfg.cap := by
    exact Nat.le_trans hqN (Nat.le_trans hn (by decide))
  have hd := g2_tableDiff_eq_and_range hflag (slotAt k).q hqCap
  have hactiveBit : p.regs rActive = 0 ∨ p.regs rActive = 1 := by
    rw [ha]
    by_cases h : (k % slots + 1) * (k % slots + 1) ≤ k / slots + 1 ∧
        (k / slots + 1) % (k % slots + 1) = 0 <;> simp [slotAt, h]
  have h := event_clean_accumulates k p g2Cfg rActive rS rQ rQ
    true false hword harray (by decide) (by decide) hactiveBit
    (by decide) (by decide) (by decide)
    (by rw [hq]; exact hqCap)
    (by decide) (by decide) (by decide) (by decide) hadd
    (by decide) (by decide) (by decide) (by decide)
    (by simpa only [hq, harr, g2Cfg, g2TableCfg] using hd.2.1)
    (by simpa only [hq, harr, g2Cfg, g2TableCfg] using hd.2.2.1)
    (by simpa only [hq, harr, g2Cfg, g2TableCfg] using hd.2.2.2.1)
    (by simpa only [hq, harr, g2Cfg, g2TableCfg] using hd.2.2.2.2)
    hr
  have hd' : tableDiff g2Cfg.cap
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr
      (slotAt k).q = referenceDiff g2G (slotAt k).q := by
    simpa only [g2Cfg, g2TableCfg, referenceDiff] using hd.1
  rw [hs, hq, ha, harr] at h
  rw [hd'] at h
  simpa only [afterFirst, firstEvent, g2Cfg, referenceDiff] using h

set_option maxRecDepth 100000 in
theorem g2_second (k : Nat) (p : AState)
    (_hk : k < productionRows * slots)
    (hword : ∀ j, p.regs j < M) (harray : ∀ j, p.arr j < M)
    (hs : p.regs rS = (slotAt k).s)
    (hq : p.regs rQ = (slotAt k).q)
    (ha : p.regs rPair = (slotAt k).pair)
    (harr : p.arr =
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr)
    (hflag : g2TableCfg.tFlag = 0)
    (hadd : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hr : EventReceipts k p g2Cfg rPair rQ rS rS true false) :
    Accumulates p (arun k p (secondEvent g2Cfg))
      (eventK1Contribution
        (divisorGate 2 (slotAt k).pair (slotAt k).q)
        (referenceDiff g2G (slotAt k).s)
        (safeDen (slotAt k).q) true).lo
      (eventK1Contribution
        (divisorGate 2 (slotAt k).pair (slotAt k).q)
        (referenceDiff g2G (slotAt k).s)
        (safeDen (slotAt k).q) true).hi
      (eventK2Contribution
        (divisorGate 2 (slotAt k).pair (slotAt k).q)
        (referenceDiff g2G (slotAt k).s) (slotAt k).s false).lo
      (eventK2Contribution
        (divisorGate 2 (slotAt k).pair (slotAt k).q)
        (referenceDiff g2G (slotAt k).s) (slotAt k).s false).hi := by
  have hsCap : (slotAt k).s ≤ g2TableCfg.cap := by
    have hm := Nat.mod_lt k (by decide : 0 < slots)
    simp only [slotAt, slots] at ⊢
    have : k % 316 + 1 ≤ 316 := by omega
    exact Nat.le_trans this (by decide)
  have hd := g2_tableDiff_eq_and_range hflag (slotAt k).s hsCap
  have hactiveBit : p.regs rPair = 0 ∨ p.regs rPair = 1 := by
    rw [ha]
    by_cases h : (k % slots + 1) * (k % slots + 1) ≤ k / slots + 1 ∧
        (k / slots + 1) % (k % slots + 1) = 0 ∧
        (k / slots + 1) / (k % slots + 1) ≠ k % slots + 1 <;>
      simp [slotAt, h]
  have h := event_clean_accumulates k p g2Cfg rPair rQ rS rS true false
    hword harray (by decide) (by decide) hactiveBit
    (by decide) (by decide) (by decide)
    (by rw [hs]; exact hsCap)
    (by decide) (by decide) (by decide) (by decide) hadd
    (by decide) (by decide) (by decide) (by decide)
    (by simpa only [hs, harr, g2Cfg, g2TableCfg] using hd.2.1)
    (by simpa only [hs, harr, g2Cfg, g2TableCfg] using hd.2.2.1)
    (by simpa only [hs, harr, g2Cfg, g2TableCfg] using hd.2.2.2.1)
    (by simpa only [hs, harr, g2Cfg, g2TableCfg] using hd.2.2.2.2)
    hr
  have hd' : tableDiff g2Cfg.cap
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr
      (slotAt k).s = referenceDiff g2G (slotAt k).s := by
    simpa only [g2Cfg, g2TableCfg, referenceDiff] using hd.1
  rw [hs, hq, ha, harr] at h
  rw [hd'] at h
  simpa only [secondEvent, g2Cfg, referenceDiff] using h

set_option maxRecDepth 100000 in
theorem g2_third (k : Nat) (p : AState)
    (hk : k < productionRows * slots)
    (hword : ∀ j, p.regs j < M) (harray : ∀ j, p.arr j < M)
    (hs : p.regs rS = (slotAt k).s)
    (hq : p.regs rHalfQ = (slotAt k).halfQ)
    (ha : p.regs rHalfActive = (slotAt k).halfActive)
    (harr : p.arr =
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr)
    (hflag : g2TableCfg.tFlag = 0)
    (hadd : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hr : EventTwiceReceipts k p g2Cfg rHalfActive rS rHalfQ rHalfQ
      false true) :
    Accumulates p (arun k p (thirdEvent g2Cfg))
      (eventK1Contribution
        (divisorGate 2 (slotAt k).halfActive (slotAt k).s)
        (referenceDiff g2G (slotAt k).halfQ)
        (safeDen (slotAt k).s * 2) false).lo
      (eventK1Contribution
        (divisorGate 2 (slotAt k).halfActive (slotAt k).s)
        (referenceDiff g2G (slotAt k).halfQ)
        (safeDen (slotAt k).s * 2) false).hi
      (eventK2Contribution
        (divisorGate 2 (slotAt k).halfActive (slotAt k).s)
        (referenceDiff g2G (slotAt k).halfQ) (slotAt k).halfQ true).lo
      (eventK2Contribution
        (divisorGate 2 (slotAt k).halfActive (slotAt k).s)
        (referenceDiff g2G (slotAt k).halfQ) (slotAt k).halfQ true).hi := by
  have hn : (slotAt k).n ≤ productionRows := by
    simp only [slotAt, productionRows, slots] at hk ⊢
    omega
  have hqN : (slotAt k).halfQ ≤ (slotAt k).n := by
    simp only [slotAt]
    exact Nat.le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)
  have hqCap : (slotAt k).halfQ ≤ g2TableCfg.cap :=
    Nat.le_trans hqN (Nat.le_trans hn (by decide))
  have hd := g2_tableDiff_eq_and_range hflag (slotAt k).halfQ hqCap
  have hactiveBit : p.regs rHalfActive = 0 ∨ p.regs rHalfActive = 1 := by
    rw [ha]
    by_cases h : (k / slots + 1) % 2 = 0 ∧
        (k % slots + 1) * (k % slots + 1) ≤ (k / slots + 1) / 2 ∧
        (k / slots + 1) / 2 % (k % slots + 1) = 0 <;>
      simp [slotAt, h]
  have hsBound : (slotAt k).s ≤ 316 := by
    have hm := Nat.mod_lt k (by decide : 0 < slots)
    simp only [slotAt, slots] at ⊢
    omega
  have htwice : safeDen (p.regs rS) * 2 < M := by
    rw [hs]
    have hsafe : safeDen (slotAt k).s ≤ 316 := by
      unfold safeDen
      split <;> omega
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 2 hsafe) (by decide)
  have h := eventTwice_clean_accumulates k p g2Cfg rHalfActive rS rHalfQ
    rHalfQ false true hword harray (by decide) (by decide) hactiveBit
    (by decide) (by decide) (by decide)
    (by rw [hq]; exact hqCap)
    (by decide) (by decide) (by decide) (by decide) htwice hadd
    (by decide) (by decide) (by decide) (by decide)
    (by simpa only [hq, harr, g2Cfg, g2TableCfg] using hd.2.1)
    (by simpa only [hq, harr, g2Cfg, g2TableCfg] using hd.2.2.1)
    (by simpa only [hq, harr, g2Cfg, g2TableCfg] using hd.2.2.2.1)
    (by simpa only [hq, harr, g2Cfg, g2TableCfg] using hd.2.2.2.2)
    hr
  have hd' : tableDiff g2Cfg.cap
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr
      (slotAt k).halfQ = referenceDiff g2G (slotAt k).halfQ := by
    simpa only [g2Cfg, g2TableCfg, referenceDiff] using hd.1
  rw [hs, hq, ha, harr] at h
  rw [hd'] at h
  simpa only [thirdEvent, g2Cfg, referenceDiff] using h

set_option maxRecDepth 100000 in
theorem g2_fourth (k : Nat) (p : AState)
    (hk : k < productionRows * slots)
    (hword : ∀ j, p.regs j < M) (harray : ∀ j, p.arr j < M)
    (hs : p.regs rS = (slotAt k).s)
    (hq : p.regs rHalfQ = (slotAt k).halfQ)
    (ha : p.regs rHalfPair = (slotAt k).halfPair)
    (harr : p.arr =
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr)
    (hflag : g2TableCfg.tFlag = 0)
    (hadd : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hr : EventTwiceReceipts k p g2Cfg rHalfPair rHalfQ rS rS false true) :
    Accumulates p (arun k p (fourthEvent g2Cfg))
      (eventK1Contribution
        (divisorGate 2 (slotAt k).halfPair (slotAt k).halfQ)
        (referenceDiff g2G (slotAt k).s)
        (safeDen (slotAt k).halfQ * 2) false).lo
      (eventK1Contribution
        (divisorGate 2 (slotAt k).halfPair (slotAt k).halfQ)
        (referenceDiff g2G (slotAt k).s)
        (safeDen (slotAt k).halfQ * 2) false).hi
      (eventK2Contribution
        (divisorGate 2 (slotAt k).halfPair (slotAt k).halfQ)
        (referenceDiff g2G (slotAt k).s) (slotAt k).s true).lo
      (eventK2Contribution
        (divisorGate 2 (slotAt k).halfPair (slotAt k).halfQ)
        (referenceDiff g2G (slotAt k).s) (slotAt k).s true).hi := by
  have hn : (slotAt k).n ≤ productionRows := by
    simp only [slotAt, productionRows, slots] at hk ⊢
    omega
  have hsCap : (slotAt k).s ≤ g2TableCfg.cap := by
    have hm := Nat.mod_lt k (by decide : 0 < slots)
    simp only [slotAt, slots] at ⊢
    have : k % 316 + 1 ≤ 316 := by omega
    exact Nat.le_trans this (by decide)
  have hd := g2_tableDiff_eq_and_range hflag (slotAt k).s hsCap
  have hactiveBit : p.regs rHalfPair = 0 ∨ p.regs rHalfPair = 1 := by
    rw [ha]
    by_cases h : (k / slots + 1) % 2 = 0 ∧
        (k % slots + 1) * (k % slots + 1) ≤ (k / slots + 1) / 2 ∧
        (k / slots + 1) / 2 % (k % slots + 1) = 0 ∧
        (k / slots + 1) / 2 / (k % slots + 1) ≠ k % slots + 1 <;>
      simp [slotAt, h]
  have hqN : (slotAt k).halfQ ≤ (slotAt k).n := by
    simp only [slotAt]
    exact Nat.le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)
  have hqBound : (slotAt k).halfQ ≤ productionRows :=
    Nat.le_trans hqN hn
  have htwice : safeDen (p.regs rHalfQ) * 2 < M := by
    rw [hq]
    have hsafe : safeDen (slotAt k).halfQ ≤ productionRows := by
      unfold safeDen
      split
      · decide
      · exact hqBound
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 2 hsafe) (by decide)
  have h := eventTwice_clean_accumulates k p g2Cfg rHalfPair rHalfQ rS rS
    false true hword harray (by decide) (by decide) hactiveBit
    (by decide) (by decide) (by decide)
    (by rw [hs]; exact hsCap)
    (by decide) (by decide) (by decide) (by decide) htwice hadd
    (by decide) (by decide) (by decide) (by decide)
    (by simpa only [hs, harr, g2Cfg, g2TableCfg] using hd.2.1)
    (by simpa only [hs, harr, g2Cfg, g2TableCfg] using hd.2.2.1)
    (by simpa only [hs, harr, g2Cfg, g2TableCfg] using hd.2.2.2.1)
    (by simpa only [hs, harr, g2Cfg, g2TableCfg] using hd.2.2.2.2)
    hr
  have hd' : tableDiff g2Cfg.cap
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr
      (slotAt k).s = referenceDiff g2G (slotAt k).s := by
    simpa only [g2Cfg, g2TableCfg, referenceDiff] using hd.1
  rw [hs, hq, ha, harr] at h
  rw [hd'] at h
  simpa only [fourthEvent, g2Cfg, referenceDiff] using h

set_option maxRecDepth 100000 in
theorem g2_body_slot (k : Nat) (p : AState)
    (hk : k < productionRows * slots)
    (hword : ∀ j, p.regs j < M) (harray : ∀ j, p.arr j < M)
    (hsched :
      p.regs rN = (slotAt k).n ∧
      p.regs rS = (slotAt k).s ∧
      p.regs rQ = (slotAt k).q ∧
      p.regs rActive = (slotAt k).active ∧
      p.regs rPair = (slotAt k).pair ∧
      p.regs rHalfQ = (slotAt k).halfQ ∧
      p.regs rHalfActive = (slotAt k).halfActive ∧
      p.regs rHalfPair = (slotAt k).halfPair)
    (harr : p.arr =
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr)
    (hflag : g2TableCfg.tFlag = 0)
    (hadd : p.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hr : EventBodyReceipts k p g2Cfg) :
    Accumulates p (arun k p (eventBody g2Cfg))
      (LeanCompCert.Ports.Section413WindowPairingBridge.k1SlotDelta
        g2G 2 (slotAt k).n (k % slots)).lo
      (LeanCompCert.Ports.Section413WindowPairingBridge.k1SlotDelta
        g2G 2 (slotAt k).n (k % slots)).hi
      (LeanCompCert.Ports.Section413WindowPairingBridge.k2SlotDelta
        g2G 2 (slotAt k).n (k % slots)).lo
      (LeanCompCert.Ports.Section413WindowPairingBridge.k2SlotDelta
        g2G 2 (slotAt k).n (k % slots)).hi := by
  let p1 := afterFirst k p g2Cfg
  let p2 := afterSecond k p g2Cfg
  let p3 := afterThird k p g2Cfg
  have hp1word : ∀ j, p1.regs j < M :=
    arun_regs_word k _ _ hword harray
  have hp1array : ∀ j, p1.arr j < M :=
    arun_arr_word k _ _ hword harray
  have hp2word : ∀ j, p2.regs j < M :=
    arun_regs_word k _ _ hp1word hp1array
  have hp2array : ∀ j, p2.arr j < M :=
    arun_arr_word k _ _ hp1word hp1array
  have hp3word : ∀ j, p3.regs j < M :=
    arun_regs_word k _ _ hp2word hp2array
  have hp3array : ∀ j, p3.arr j < M :=
    arun_arr_word k _ _ hp2word hp2array
  have frame1 (r : Nat) (hw : LeanCompCert.Verified.ArrayRegFrame.writes r
      (firstEvent g2Cfg) = false) : p1.regs r = p.regs r := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k r _ hw p
  have frame2 (r : Nat) (hw : LeanCompCert.Verified.ArrayRegFrame.writes r
      (firstEvent g2Cfg ++ secondEvent g2Cfg) = false) :
      p2.regs r = p.regs r := by
    simpa only [p2, p1, afterSecond, afterFirst, arun_append] using
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k r _ hw p
  have frame3 (r : Nat) (hw : LeanCompCert.Verified.ArrayRegFrame.writes r
      (firstEvent g2Cfg ++ secondEvent g2Cfg ++ thirdEvent g2Cfg) = false) :
      p3.regs r = p.regs r := by
    simpa only [p3, p2, p1, afterThird, afterSecond, afterFirst,
      arun_append] using
      LeanCompCert.Verified.ArrayRegFrame.arun_frame k r _ hw p
  have h1 := g2_first k p hk hword harray hsched.2.1 hsched.2.2.1
    hsched.2.2.2.1 harr hflag hadd hr.first
  have h2 := g2_second k p1 hk hp1word hp1array
    ((frame1 rS (by decide)).trans hsched.2.1)
    ((frame1 rQ (by decide)).trans hsched.2.2.1)
    ((frame1 rPair (by decide)).trans hsched.2.2.2.2.1)
    (h1.array_eq.trans harr) hflag h1.add_clean hr.second
  have h3 := g2_third k p2 hk hp2word hp2array
    ((frame2 rS (by decide)).trans hsched.2.1)
    ((frame2 rHalfQ (by decide)).trans hsched.2.2.2.2.2.1)
    ((frame2 rHalfActive (by decide)).trans hsched.2.2.2.2.2.2.1)
    (h2.array_eq.trans (h1.array_eq.trans harr)) hflag h2.add_clean hr.third
  have h4 := g2_fourth k p3 hk hp3word hp3array
    ((frame3 rS (by decide)).trans hsched.2.1)
    ((frame3 rHalfQ (by decide)).trans hsched.2.2.2.2.2.1)
    ((frame3 rHalfPair (by decide)).trans hsched.2.2.2.2.2.2.2)
    (h3.array_eq.trans (h2.array_eq.trans (h1.array_eq.trans harr)))
    hflag h3.add_clean hr.fourth
  have hbody := eventBody_accumulates k p g2Cfg _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ h1 h2 h3 h4
  have hok1 := ordinaryK1 g2G 2 (slotAt k).n (k % slots) (Or.inr rfl)
  have hok2 := ordinaryK2 g2G 2 (slotAt k).n (k % slots) (Or.inr rfl)
  have hhk1 := halfK1 g2G 2 (slotAt k).n (k % slots) (Or.inr rfl)
  have hhk2 := halfK2 g2G 2 (slotAt k).n (k % slots) (Or.inr rfl)
  let a1 := eventK1Contribution
    (divisorGate 2 (slotAt k).active (slotAt k).s)
    (referenceDiff g2G (slotAt k).q) (safeDen (slotAt k).s) true
  let a2 := eventK1Contribution
    (divisorGate 2 (slotAt k).pair (slotAt k).q)
    (referenceDiff g2G (slotAt k).s) (safeDen (slotAt k).q) true
  let a3 := eventK1Contribution
    (divisorGate 2 (slotAt k).halfActive (slotAt k).s)
    (referenceDiff g2G (slotAt k).halfQ) (safeDen (slotAt k).s * 2) false
  let a4 := eventK1Contribution
    (divisorGate 2 (slotAt k).halfPair (slotAt k).halfQ)
    (referenceDiff g2G (slotAt k).s) (safeDen (slotAt k).halfQ * 2) false
  let b1 := eventK2Contribution
    (divisorGate 2 (slotAt k).active (slotAt k).s)
    (referenceDiff g2G (slotAt k).q) (slotAt k).q false
  let b2 := eventK2Contribution
    (divisorGate 2 (slotAt k).pair (slotAt k).q)
    (referenceDiff g2G (slotAt k).s) (slotAt k).s false
  let b3 := eventK2Contribution
    (divisorGate 2 (slotAt k).halfActive (slotAt k).s)
    (referenceDiff g2G (slotAt k).halfQ) (slotAt k).halfQ true
  let b4 := eventK2Contribution
    (divisorGate 2 (slotAt k).halfPair (slotAt k).halfQ)
    (referenceDiff g2G (slotAt k).s) (slotAt k).s true
  change cadd a1 a2 = _ at hok1
  change cadd a3 a4 = _ at hhk1
  change cadd b1 b2 = _ at hok2
  change cadd b3 b4 = _ at hhk2
  have hk1lo : (((a1.lo + a2.lo) + a3.lo) + a4.lo) =
      (LeanCompCert.Ports.Section413WindowPairingBridge.k1SlotDelta
        g2G 2 (slotAt k).n (k % slots)).lo := by
    calc
      (((a1.lo + a2.lo) + a3.lo) + a4.lo) =
          (cadd (cadd a1 a2) (cadd a3 a4)).lo := by simp [cadd, Int.add_assoc]
      _ = (cadd
          (LeanCompCert.Ports.Section413WindowPairingBridge.slotDelta 2
            (slotAt k).n (k1First g2G (slotAt k).n) (k % slots))
          (if (slotAt k).n % 2 = 0 then
            LeanCompCert.Ports.Section413WindowPairingBridge.slotDelta 2
              ((slotAt k).n / 2) (k1Second g2G ((slotAt k).n / 2))
              (k % slots) else czero)).lo := by rw [hok1, hhk1]
      _ = _ := rfl
  have hk1hi : (((a1.hi + a2.hi) + a3.hi) + a4.hi) =
      (LeanCompCert.Ports.Section413WindowPairingBridge.k1SlotDelta
        g2G 2 (slotAt k).n (k % slots)).hi := by
    calc
      (((a1.hi + a2.hi) + a3.hi) + a4.hi) =
          (cadd (cadd a1 a2) (cadd a3 a4)).hi := by simp [cadd, Int.add_assoc]
      _ = (cadd
          (LeanCompCert.Ports.Section413WindowPairingBridge.slotDelta 2
            (slotAt k).n (k1First g2G (slotAt k).n) (k % slots))
          (if (slotAt k).n % 2 = 0 then
            LeanCompCert.Ports.Section413WindowPairingBridge.slotDelta 2
              ((slotAt k).n / 2) (k1Second g2G ((slotAt k).n / 2))
              (k % slots) else czero)).hi := by rw [hok1, hhk1]
      _ = _ := rfl
  have hk2lo : (((b1.lo + b2.lo) + b3.lo) + b4.lo) =
      (LeanCompCert.Ports.Section413WindowPairingBridge.k2SlotDelta
        g2G 2 (slotAt k).n (k % slots)).lo := by
    calc
      (((b1.lo + b2.lo) + b3.lo) + b4.lo) =
          (cadd (cadd b1 b2) (cadd b3 b4)).lo := by simp [cadd, Int.add_assoc]
      _ = (cadd
          (LeanCompCert.Ports.Section413WindowPairingBridge.slotDelta 2
            (slotAt k).n (k2First g2G (slotAt k).n) (k % slots))
          (if (slotAt k).n % 2 = 0 then
            LeanCompCert.Ports.Section413WindowPairingBridge.slotDelta 2
              ((slotAt k).n / 2) (k2Second g2G ((slotAt k).n / 2))
              (k % slots) else czero)).lo := by rw [hok2, hhk2]
      _ = _ := rfl
  have hk2hi : (((b1.hi + b2.hi) + b3.hi) + b4.hi) =
      (LeanCompCert.Ports.Section413WindowPairingBridge.k2SlotDelta
        g2G 2 (slotAt k).n (k % slots)).hi := by
    calc
      (((b1.hi + b2.hi) + b3.hi) + b4.hi) =
          (cadd (cadd b1 b2) (cadd b3 b4)).hi := by simp [cadd, Int.add_assoc]
      _ = (cadd
          (LeanCompCert.Ports.Section413WindowPairingBridge.slotDelta 2
            (slotAt k).n (k2First g2G (slotAt k).n) (k % slots))
          (if (slotAt k).n % 2 = 0 then
            LeanCompCert.Ports.Section413WindowPairingBridge.slotDelta 2
              ((slotAt k).n / 2) (k2Second g2G ((slotAt k).n / 2))
              (k % slots) else czero)).hi := by rw [hok2, hhk2]
      _ = _ := rfl
  apply Accumulates.of_outputs
  refine ⟨?_, ?_, ?_, ?_, hbody.scale_clean, hbody.add_clean,
    hbody.array_eq⟩
  · rw [hbody.k1Lo_eq]
    exact congrArg (fun z => decodeZ (p.regs rK1Lo) + z) hk1lo
  · rw [hbody.k1Hi_eq]
    exact congrArg (fun z => decodeZ (p.regs rK1Hi) + z) hk1hi
  · rw [hbody.k2Lo_eq]
    exact congrArg (fun z => decodeZ (p.regs rK2Lo) + z) hk2lo
  · rw [hbody.k2Hi_eq]
    exact congrArg (fun z => decodeZ (p.regs rK2Hi) + z) hk2hi

#print axioms g2_first
#print axioms g2_second
#print axioms g2_third
#print axioms g2_fourth
#print axioms g2_body_slot

end LeanCompCert.Ports.Section413WindowBodyReferenceSoundG2

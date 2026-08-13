import LeanCompCert.Ports.Section413WindowScannerReferenceFold
import LeanCompCert.Ports.Section413WindowScannerReferenceStepG2

/-!
# Symbolic compiled G2 scanner fold matches paper slot prefixes

This induction is over an abstract prefix length.  It consumes one compact
event receipt per symbolic step and never normalizes the concrete production
range.
-/

namespace LeanCompCert.Ports.Section413WindowScannerReferenceFoldG2
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413Cells
open LeanCompCert.Ports.Section413WindowEventScanner
open LeanCompCert.Ports.Section413WindowPipelineSound
open LeanCompCert.Ports.Section413WindowTableReferenceBridge
open LeanCompCert.Ports.Section413WindowScannerReferenceStepG2
open LeanCompCert.Ports.Section413WindowSchedule

def flatK1Prefix (G : Nat → Cell) (v n : Nat) : Cell :=
  (List.range n).foldl (fun z k => cadd z
    (LeanCompCert.Ports.Section413WindowPairingBridge.k1SlotDelta
      G v (slotAt k).n (k % slots))) czero

def flatK2Prefix (G : Nat → Cell) (v n : Nat) : Cell :=
  (List.range n).foldl (fun z k => cadd z
    (LeanCompCert.Ports.Section413WindowPairingBridge.k2SlotDelta
      G v (slotAt k).n (k % slots))) czero

theorem flatK1Prefix_succ (G : Nat → Cell) (v n : Nat) :
    flatK1Prefix G v (n + 1) = cadd (flatK1Prefix G v n)
      (LeanCompCert.Ports.Section413WindowPairingBridge.k1SlotDelta
        G v (slotAt n).n (n % slots)) := by
  simp [flatK1Prefix, List.range_succ, List.foldl_append]

theorem flatK2Prefix_succ (G : Nat → Cell) (v n : Nat) :
    flatK2Prefix G v (n + 1) = cadd (flatK2Prefix G v n)
      (LeanCompCert.Ports.Section413WindowPairingBridge.k2SlotDelta
        G v (slotAt n).n (n % slots)) := by
  simp [flatK2Prefix, List.range_succ, List.foldl_append]

theorem flatK1Prefix_eq_reference (G : Nat → Cell) (v n : Nat) :
    flatK1Prefix G v n =
      LeanCompCert.Ports.Section413WindowScannerReferenceFold.flatK1Prefix
        G v n := rfl

theorem flatK2Prefix_eq_reference (G : Nat → Cell) (v n : Nat) :
    flatK2Prefix G v n =
      LeanCompCert.Ports.Section413WindowScannerReferenceFold.flatK2Prefix
        G v n := rfl

theorem flatK1Prefix_rows (G : Nat → Cell) (v n : Nat)
    (hn : n ≤ productionRows) :
    flatK1Prefix G v (n * slots) =
      LeanCompCert.Ports.Section413WindowScannerReferenceFold.rowK1Prefix
        G v n := by
  rw [flatK1Prefix_eq_reference]
  exact
    LeanCompCert.Ports.Section413WindowScannerReferenceFold.flatK1Prefix_rows
      G v n hn

theorem flatK2Prefix_rows (G : Nat → Cell) (v n : Nat)
    (hn : n ≤ productionRows) :
    flatK2Prefix G v (n * slots) =
      LeanCompCert.Ports.Section413WindowScannerReferenceFold.rowK2Prefix
        G v n := by
  rw [flatK2Prefix_eq_reference]
  exact
    LeanCompCert.Ports.Section413WindowScannerReferenceFold.flatK2Prefix_rows
      G v n hn

theorem body_eq_checked (k : Nat) (s : AState) (c : Cfg) :
    arun k s (body c) = checkedState k s c := by
  rw [body_split, arun_append, arun_append]
  rfl

structure G2Matches (entry : AState) (n : Nat) : Prop where
  k1lo : decodeZ ((scannerStateAt g2Cfg entry n).regs rK1Lo) =
    (flatK1Prefix g2G 2 n).lo
  k1hi : decodeZ ((scannerStateAt g2Cfg entry n).regs rK1Hi) =
    (flatK1Prefix g2G 2 n).hi
  k2lo : decodeZ ((scannerStateAt g2Cfg entry n).regs rK2Lo) =
    (flatK2Prefix g2G 2 n).lo
  k2hi : decodeZ ((scannerStateAt g2Cfg entry n).regs rK2Hi) =
    (flatK2Prefix g2G 2 n).hi
  array_eq : (scannerStateAt g2Cfg entry n).arr =
    (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr

set_option maxRecDepth 100000 in
theorem g2_scanner_prefix_matches (entry : AState)
    (hword : ∀ j, entry.regs j < M) (harray : ∀ j, entry.arr j < M)
    (hentryK : decodeZ (entry.regs rK1Lo) = 0 ∧
      decodeZ (entry.regs rK1Hi) = 0 ∧
      decodeZ (entry.regs rK2Lo) = 0 ∧
      decodeZ (entry.regs rK2Hi) = 0)
    (hentryArr : entry.arr =
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr)
    (hflag : g2TableCfg.tFlag = 0)
    (n : Nat) (hn : n ≤ productionRows * slots)
    (hclean : ∀ k, k ≤ n →
      (scannerStateAt g2Cfg entry k).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hreceipts : ∀ k, k < n → EventBodyReceipts k
      (scheduledState k (scannerStateAt g2Cfg entry k)) g2Cfg) :
    G2Matches entry n := by
  induction n with
  | zero =>
      constructor
      · simpa [flatK1Prefix, czero] using hentryK.1
      · simpa [flatK1Prefix, czero] using hentryK.2.1
      · simpa [flatK2Prefix, czero] using hentryK.2.2.1
      · simpa [flatK2Prefix, czero] using hentryK.2.2.2
      · exact hentryArr
  | succ n ih =>
      have hnlt : n < productionRows * slots := by omega
      have hprev := ih (by omega) (fun k hk => hclean k (by omega))
        (fun k hk => hreceipts k (by omega))
      have hsword := scannerStateAt_word g2Cfg entry hword harray n
      have hpadd : (scheduledState n (scannerStateAt g2Cfg entry n)).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
        rw [scheduledState,
          LeanCompCert.Verified.ArrayRegFrame.arun_frame n
            LeanCompCert.Ports.Section413SignedAdd.rViol
            LeanCompCert.Ports.Section413WindowSchedule.body (by decide)]
        exact hclean n (by omega)
      have htadd : (checkedState n (scannerStateAt g2Cfg entry n) g2Cfg).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
        rw [← body_eq_checked, ← scannerStateAt_succ]
        exact hclean (n + 1) (Nat.le_refl _)
      have hs := g2_scanner_step n (scannerStateAt g2Cfg entry n) hnlt
        hsword.1 hsword.2 hprev.array_eq hflag hpadd htadd
        (hreceipts n (by omega))
      rw [← body_eq_checked, ← scannerStateAt_succ] at hs
      constructor
      · rw [hs.k1Lo_eq, hprev.k1lo, flatK1Prefix_succ]
        rfl
      · rw [hs.k1Hi_eq, hprev.k1hi, flatK1Prefix_succ]
        rfl
      · rw [hs.k2Lo_eq, hprev.k2lo, flatK2Prefix_succ]
        rfl
      · rw [hs.k2Hi_eq, hprev.k2hi, flatK2Prefix_succ]
        rfl
      · exact hs.array_eq.trans hprev.array_eq

#print axioms flatK1Prefix_succ
#print axioms flatK2Prefix_succ
#print axioms flatK1Prefix_rows
#print axioms flatK2Prefix_rows
#print axioms body_eq_checked
#print axioms g2_scanner_prefix_matches

end LeanCompCert.Ports.Section413WindowScannerReferenceFoldG2

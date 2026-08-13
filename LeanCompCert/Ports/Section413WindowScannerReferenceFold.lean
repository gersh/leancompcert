import LeanCompCert.Ports.Section413WindowScannerReferenceStep
import LeanCompCert.Ports.Section413WindowScannerReferenceStepG2

/-!
# Symbolic compiled scanner fold matches paper slot prefixes

This induction is over an abstract prefix length.  It consumes one compact
event receipt per symbolic step and never normalizes the concrete production
range.
-/

namespace LeanCompCert.Ports.Section413WindowScannerReferenceFold
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413Cells
open LeanCompCert.Ports.Section413WindowEventScanner
open LeanCompCert.Ports.Section413WindowPipelineSound
open LeanCompCert.Ports.Section413WindowTableReferenceBridge
open LeanCompCert.Ports.Section413WindowScannerReferenceStep
open LeanCompCert.Ports.Section413WindowSchedule
open LeanCompCert.Ports.Section413WindowPairingBridge

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

private theorem cadd_assoc (a b c : Cell) :
    cadd (cadd a b) c = cadd a (cadd b c) := by
  cases a; cases b; cases c
  simp [cadd, Int.add_assoc]

private theorem cadd_zero (a : Cell) : cadd a czero = a := by
  cases a
  simp [cadd, czero]

private theorem zero_cadd (a : Cell) : cadd czero a = a := by
  cases a
  simp [cadd, czero]

private theorem foldCadd_start (xs : List Nat) (f : Nat → Cell)
    (a : Cell) :
    xs.foldl (fun z i => cadd z (f i)) a =
      cadd a (xs.foldl (fun z i => cadd z (f i)) czero) := by
  induction xs generalizing a with
  | nil => simp [cadd_zero]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih (cadd a (f i))]
      rw [zero_cadd, ih (f i), cadd_assoc]

theorem slotAt_block (r i : Nat) (hi : i < slots) :
    (slotAt (r * slots + i)).n = r + 1 ∧
      (r * slots + i) % slots = i := by
  have hi316 : i < 316 := by simpa [slots] using hi
  constructor
  · simp [slotAt, slots, Nat.add_div, Nat.add_mod,
      Nat.div_eq_of_lt hi316, Nat.mod_eq_of_lt hi316]
    exact hi316
  · simpa [slots] using hi316

private theorem foldl_eq_of_mem (xs : List Nat)
    (f g : Cell → Nat → Cell) (a : Cell)
    (h : ∀ i ∈ xs, ∀ z, f z i = g z i) :
    xs.foldl f a = xs.foldl g a := by
  induction xs generalizing a with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [h i (by simp)]
      apply ih
      intro j hj
      exact h j (by simp [hj])

private theorem blockK1 (G : Nat → Cell) (v r : Nat) :
    (List.range slots).foldl
        (fun z i => cadd z (k1SlotDelta G v
          (slotAt (r * slots + i)).n ((r * slots + i) % slots))) czero =
      k1Slots slots G v (r + 1) := by
  unfold k1Slots
  apply foldl_eq_of_mem
  intro i hi a
  have hi' : i < slots := List.mem_range.mp hi
  rw [(slotAt_block r i hi').1, (slotAt_block r i hi').2]

private theorem blockK2 (G : Nat → Cell) (v r : Nat) :
    (List.range slots).foldl
        (fun z i => cadd z (k2SlotDelta G v
          (slotAt (r * slots + i)).n ((r * slots + i) % slots))) czero =
      k2Slots slots G v (r + 1) := by
  unfold k2Slots
  apply foldl_eq_of_mem
  intro i hi a
  have hi' : i < slots := List.mem_range.mp hi
  rw [(slotAt_block r i hi').1, (slotAt_block r i hi').2]

theorem flatK1Prefix_block (G : Nat → Cell) (v r : Nat) :
    flatK1Prefix G v ((r + 1) * slots) =
      cadd (flatK1Prefix G v (r * slots))
        (k1Slots slots G v (r + 1)) := by
  rw [show (r + 1) * slots = r * slots + slots by simp [Nat.add_mul]]
  unfold flatK1Prefix
  rw [List.range_add, List.foldl_append, List.foldl_map]
  rw [foldCadd_start, blockK1]

theorem flatK2Prefix_block (G : Nat → Cell) (v r : Nat) :
    flatK2Prefix G v ((r + 1) * slots) =
      cadd (flatK2Prefix G v (r * slots))
        (k2Slots slots G v (r + 1)) := by
  rw [show (r + 1) * slots = r * slots + slots by simp [Nat.add_mul]]
  unfold flatK2Prefix
  rw [List.range_add, List.foldl_append, List.foldl_map]
  rw [foldCadd_start, blockK2]

def rowK1Prefix (G : Nat → Cell) (v n : Nat) : Cell :=
  (List.range n).foldl
    (fun z r => cadd z (k1Delta G v (r + 1))) czero

def rowK2Prefix (G : Nat → Cell) (v n : Nat) : Cell :=
  (List.range n).foldl
    (fun z r => cadd z (k2Delta G v (r + 1))) czero

theorem rowK1Prefix_succ (G : Nat → Cell) (v n : Nat) :
    rowK1Prefix G v (n + 1) =
      cadd (rowK1Prefix G v n) (k1Delta G v (n + 1)) := by
  simp [rowK1Prefix, List.range_succ, List.foldl_append]

theorem rowK2Prefix_succ (G : Nat → Cell) (v n : Nat) :
    rowK2Prefix G v (n + 1) =
      cadd (rowK2Prefix G v n) (k2Delta G v (n + 1)) := by
  simp [rowK2Prefix, List.range_succ, List.foldl_append]

theorem flatK1Prefix_rows (G : Nat → Cell) (v n : Nat)
    (hn : n ≤ productionRows) :
    flatK1Prefix G v (n * slots) = rowK1Prefix G v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [flatK1Prefix_block, rowK1Prefix_succ, ih (by omega)]
      rw [k1Slots_eq_k1Delta]
      · exact production_sqrt_le_slots (n + 1) (by omega)
      · exact production_sqrt_le_slots ((n + 1) / 2) (by omega)

theorem flatK2Prefix_rows (G : Nat → Cell) (v n : Nat)
    (hn : n ≤ productionRows) :
    flatK2Prefix G v (n * slots) = rowK2Prefix G v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [flatK2Prefix_block, rowK2Prefix_succ, ih (by omega)]
      rw [k2Slots_eq_k2Delta]
      · exact production_sqrt_le_slots (n + 1) (by omega)
      · exact production_sqrt_le_slots ((n + 1) / 2) (by omega)

theorem kRun_components (G : Nat → Cell) (v lo : Nat)
    (boundNum : Int) (boundDen n : Nat) :
    (kRun G v lo boundNum boundDen n).k1 = rowK1Prefix G v n ∧
      (kRun G v lo boundNum boundDen n).k2 = rowK2Prefix G v n := by
  unfold kRun
  induction n with
  | zero => constructor <;> rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      constructor
      · change cadd
          (List.foldl (fun p i => kStep G v lo boundNum boundDen i p)
            ⟨czero, czero, true⟩ (List.range n)).k1
          (k1Delta G v (n + 1)) = rowK1Prefix G v (n + 1)
        rw [ih.1, rowK1Prefix_succ]
      · change cadd
          (List.foldl (fun p i => kStep G v lo boundNum boundDen i p)
            ⟨czero, czero, true⟩ (List.range n)).k2
          (k2Delta G v (n + 1)) = rowK2Prefix G v (n + 1)
        rw [ih.2, rowK2Prefix_succ]

theorem body_eq_checked (k : Nat) (s : AState) (c : Cfg) :
    arun k s (body c) = checkedState k s c := by
  rw [body_split, arun_append, arun_append]
  rfl

structure G1Matches (entry : AState) (n : Nat) : Prop where
  k1lo : decodeZ ((scannerStateAt g1Cfg entry n).regs rK1Lo) =
    (flatK1Prefix g1G 1 n).lo
  k1hi : decodeZ ((scannerStateAt g1Cfg entry n).regs rK1Hi) =
    (flatK1Prefix g1G 1 n).hi
  k2lo : decodeZ ((scannerStateAt g1Cfg entry n).regs rK2Lo) =
    (flatK2Prefix g1G 1 n).lo
  k2hi : decodeZ ((scannerStateAt g1Cfg entry n).regs rK2Hi) =
    (flatK2Prefix g1G 1 n).hi
  array_eq : (scannerStateAt g1Cfg entry n).arr =
    (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr

set_option maxRecDepth 100000 in
theorem g1_scanner_prefix_matches (entry : AState)
    (hword : ∀ j, entry.regs j < M) (harray : ∀ j, entry.arr j < M)
    (hentryK : decodeZ (entry.regs rK1Lo) = 0 ∧
      decodeZ (entry.regs rK1Hi) = 0 ∧
      decodeZ (entry.regs rK2Lo) = 0 ∧
      decodeZ (entry.regs rK2Hi) = 0)
    (hentryArr : entry.arr =
      (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr)
    (hflag : g1TableCfg.tFlag = 0)
    (n : Nat) (hn : n ≤ productionRows * slots)
    (hclean : ∀ k, k ≤ n →
      (scannerStateAt g1Cfg entry k).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0)
    (hreceipts : ∀ k, k < n → EventBodyReceipts k
      (scheduledState k (scannerStateAt g1Cfg entry k)) g1Cfg) :
    G1Matches entry n := by
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
      have hsword := scannerStateAt_word g1Cfg entry hword harray n
      have hpadd : (scheduledState n (scannerStateAt g1Cfg entry n)).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
        rw [scheduledState,
          LeanCompCert.Verified.ArrayRegFrame.arun_frame n
            LeanCompCert.Ports.Section413SignedAdd.rViol
            LeanCompCert.Ports.Section413WindowSchedule.body (by decide)]
        exact hclean n (by omega)
      have htadd : (checkedState n (scannerStateAt g1Cfg entry n) g1Cfg).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
        rw [← body_eq_checked, ← scannerStateAt_succ]
        exact hclean (n + 1) (Nat.le_refl _)
      have hs := g1_scanner_step n (scannerStateAt g1Cfg entry n) hnlt
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
#print axioms kRun_components
#print axioms body_eq_checked
#print axioms g1_scanner_prefix_matches

end LeanCompCert.Ports.Section413WindowScannerReferenceFold

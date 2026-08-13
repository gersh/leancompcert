import LeanCompCert.Ports.Section413Window99999PipelineReceipt
import LeanCompCert.Ports.Section413WindowScannerReferenceFold
import LeanCompCert.Ports.Section413WindowScannerReferenceFoldG2

/-!
# Compact Section 4.1.3 receipt refines the reference folds

The physical receipt contains only the rolled CompCert traces and zero
outputs.  The proofs below recover the complete scanner-prefix invariant by
symbolic induction.  They never materialise or normalize the production
tables or the `99,999 * 316` scanner iterations in Lean.
-/

namespace LeanCompCert.Ports.Section413Window99999ReferenceFold

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.Section413Cells
open LeanCompCert.Ports.Section413WindowEventScanner
open LeanCompCert.Ports.Section413WindowPipelineSound
open LeanCompCert.Ports.Section413WindowTableReferenceBridge
open LeanCompCert.Ports.Section413WindowSchedule

/-- The constant-size scanner initializer sets the four reference
accumulators to zero and leaves the caller-owned producer table unchanged. -/
theorem initial_reference_state (arr : Nat → Nat) :
    let entry := arun 0 (initialAStateWithArray arr) init
    decodeZ (entry.regs rK1Lo) = 0 ∧
      decodeZ (entry.regs rK1Hi) = 0 ∧
      decodeZ (entry.regs rK2Lo) = 0 ∧
      decodeZ (entry.regs rK2Hi) = 0 ∧ entry.arr = arr := by
  dsimp only
  rw [init, arun_append, eventInit,
    LeanCompCert.Ports.Section413WindowRowCheck.init, arun_lift, arun_lift]
  simp [srun, sdest, sval, denoteOperand, RegState.set,
    initialAStateWithArray, decodeZ,
    LeanCompCert.Ports.Section413Cells.H63]

private theorem initial_words (arr : Nat → Nat) (harr : ∀ j, arr j < M) :
    let entry := arun 0 (initialAStateWithArray arr) init
    (∀ j, entry.regs j < M) ∧ (∀ j, entry.arr j < M) := by
  dsimp only
  have hw : ∀ j, (initialAStateWithArray arr).regs j < M := by
    intro j
    simp [initialAStateWithArray, initialState, M]
  have ha : ∀ j, (initialAStateWithArray arr).arr j < M := by
    intro j
    simpa only [initialAStateWithArray] using harr j
  exact ⟨arun_regs_word 0 _ _ hw ha, arun_arr_word 0 _ _ hw ha⟩

private theorem g1_array_word : ∀ j,
    (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr j <
      M := by
  rw [LeanCompCert.Ports.Section413G1TableSound.rawFinal_eq_prefix]
  exact (LeanCompCert.Ports.Section413G1TableSound.rawPrefix_wordInv
    g1TableCfg g1TableCfg_admissible g1TableCfg.loopCount
      (Nat.le_refl _)).2

private theorem g2_array_word : ∀ j,
    (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr j <
      M := by
  rw [LeanCompCert.Ports.Section413G2TableSound.rawFinal_eq_prefix]
  exact (LeanCompCert.Ports.Section413G2TableSound.rawPrefix_wordInv
    g2TableCfg g2TableCfg_admissible g2TableCfg.loopCount
      (Nat.le_refl _)).2

set_option maxRecDepth 100000 in
theorem g1_full_scanner_prefix (out : AState)
    (hflagRaw : (LeanCompCert.Ports.Section413G1TableProgram.rawFinal
      g1TableCfg).regs LeanCompCert.Ports.Section413G1Program.rViol = 0)
    (hrun : g1Scanner.runFromArray
      (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr =
        some out)
    (hzero : out.regs g1Scanner.output = 0)
    (hreceipts : ∀ k, k < g1Cfg.rows * slots →
      EventBodyReceipts k
        (scheduledState k (scannerStateAt g1Cfg
          (arun 0 (initialAStateWithArray
            (LeanCompCert.Ports.Section413G1TableProgram.rawFinal
              g1TableCfg).arr) init) k)) g1Cfg) :
    LeanCompCert.Ports.Section413WindowScannerReferenceFold.G1Matches
      (arun 0 (initialAStateWithArray
        (LeanCompCert.Ports.Section413G1TableProgram.rawFinal
          g1TableCfg).arr) init) (g1Cfg.rows * slots) := by
  let arr :=
    (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr
  let entry := arun 0 (initialAStateWithArray arr) init
  have hi := initial_reference_state arr
  have hw := initial_words arr g1_array_word
  have hclean : ∀ k, k ≤ g1Cfg.rows * slots →
      (scannerStateAt g1Cfg entry k).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    apply program_runFromArray_zero_implies_add_prefix_clean g1Cfg arr
      g1_array_word (by decide) (by decide) (by decide) (by decide)
      (by decide) g1EventDefinedFrames g1EventBodyFrames (by decide)
      (by decide) out
    · simpa only [g1Scanner, arr] using hrun
    · simpa only [g1Scanner] using hzero
  apply
    LeanCompCert.Ports.Section413WindowScannerReferenceFold.g1_scanner_prefix_matches
      entry hw.1 hw.2 ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1⟩
      hi.2.2.2.2 (g1_flag_zero hflagRaw) (g1Cfg.rows * slots)
      (by decide) hclean
  intro k hk
  simpa only [entry, arr] using hreceipts k hk

set_option maxRecDepth 100000 in
theorem g2_full_scanner_prefix (out : AState)
    (hflagRaw : (LeanCompCert.Ports.Section413G2TableProgram.rawFinal
      g2TableCfg).regs LeanCompCert.Ports.Section413G2Program.rViol = 0)
    (hrun : g2Scanner.runFromArray
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr =
        some out)
    (hzero : out.regs g2Scanner.output = 0)
    (hreceipts : ∀ k, k < g2Cfg.rows * slots →
      EventBodyReceipts k
        (scheduledState k (scannerStateAt g2Cfg
          (arun 0 (initialAStateWithArray
            (LeanCompCert.Ports.Section413G2TableProgram.rawFinal
              g2TableCfg).arr) init) k)) g2Cfg) :
    LeanCompCert.Ports.Section413WindowScannerReferenceFoldG2.G2Matches
      (arun 0 (initialAStateWithArray
        (LeanCompCert.Ports.Section413G2TableProgram.rawFinal
          g2TableCfg).arr) init) (g2Cfg.rows * slots) := by
  let arr :=
    (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr
  let entry := arun 0 (initialAStateWithArray arr) init
  have hi := initial_reference_state arr
  have hw := initial_words arr g2_array_word
  have hclean : ∀ k, k ≤ g2Cfg.rows * slots →
      (scannerStateAt g2Cfg entry k).regs
        LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
    apply program_runFromArray_zero_implies_add_prefix_clean g2Cfg arr
      g2_array_word (by decide) (by decide) (by decide) (by decide)
      (by decide) g2EventDefinedFrames g2EventBodyFrames (by decide)
      (by decide) out
    · simpa only [g2Scanner, arr] using hrun
    · simpa only [g2Scanner] using hzero
  apply
    LeanCompCert.Ports.Section413WindowScannerReferenceFoldG2.g2_scanner_prefix_matches
      entry hw.1 hw.2 ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1⟩
      hi.2.2.2.2 (g2_flag_zero hflagRaw) (g2Cfg.rows * slots)
      (by decide) hclean
  intro k hk
  simpa only [entry, arr] using hreceipts k hk

set_option maxRecDepth 100000 in
/-- The compact physical receipt proves the complete G1 and G2 reference
prefixes at the production endpoint. -/
theorem full_scanner_prefixes
    (h : LeanCompCert.Ports.Section413Window99999PipelineReceipt.Receipt) :
    let table1 := LeanCompCert.Ports.Section413G1TableProgram.rawFinal
      g1TableCfg
    let entry1 := arun 0 (initialAStateWithArray table1.arr) init
    let table2 := LeanCompCert.Ports.Section413G2TableProgram.rawFinal
      g2TableCfg
    let entry2 := arun 0 (initialAStateWithArray table2.arr) init
    LeanCompCert.Ports.Section413WindowScannerReferenceFold.G1Matches entry1
        (g1Cfg.rows * slots) ∧
      LeanCompCert.Ports.Section413WindowScannerReferenceFoldG2.G2Matches entry2
        (g2Cfg.rows * slots) := by
  dsimp only
  obtain ⟨⟨hflag1raw, out1, hrun1, hzero1⟩,
      ⟨hflag2raw, out2, hrun2, hzero2⟩⟩ :=
    LeanCompCert.Ports.Section413Window99999PipelineReceipt.source_runs h
  obtain ⟨hreceipts1, hreceipts2⟩ :=
    LeanCompCert.Ports.Section413Window99999PipelineReceipt.event_receipts_and_bounds h
  constructor
  · apply g1_full_scanner_prefix out1 hflag1raw hrun1 hzero1
    intro k hk
    exact (hreceipts1 k hk).1
  · apply g2_full_scanner_prefix out2 hflag2raw hrun2 hzero2
    intro k hk
    exact (hreceipts2 k hk).1

#print axioms initial_reference_state
#print axioms g1_full_scanner_prefix
#print axioms g2_full_scanner_prefix
#print axioms full_scanner_prefixes

end LeanCompCert.Ports.Section413Window99999ReferenceFold

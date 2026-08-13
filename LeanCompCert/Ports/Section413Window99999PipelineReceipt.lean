import LeanCompCert.Ports.Section413WindowPipelineSound

/-!
# Compact physical receipt for the Section 4.1.3 production window

The external artifact executes four rolled CompCert traces over two
caller-owned arrays: a G1 table producer and scanner, followed by their G2
counterparts.  This file states that physical result without materialising a
table or event word in Lean, then derives the uniform source-level event
receipts and paper bounds.
-/

namespace LeanCompCert.Ports.Section413Window99999PipelineReceipt

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.Section413WindowPipelineSound

/-- The complete constant-size receipt recorded from the physical pipeline.
Only the two producer final states and four trace/output equalities are
retained; the 100,000-cell tables and 31,599,684 scanner iterations stay in
compiled memory. -/
def Receipt : Prop :=
  ∃ g1ProducerOut g2ProducerOut : MCCState,
    evalMCCSequence
      (g1Producer.counterAugment.initialMCCWithMem 0
        (initialMem g1Producer.arrayLen 0))
      g1Producer.rolledCompile = some g1ProducerOut ∧
    g1ProducerOut.env ⟨g1Producer.output + 1⟩ = some (0 : Int) ∧
    Option.bind
      (evalMCCSequence
        (g1Scanner.counterAugment.initialMCCWithMem 0 g1ProducerOut.mem)
        g1Scanner.rolledCompile)
      (fun m : MCCState => m.env ⟨g1Scanner.output + 1⟩) = some (0 : Int) ∧
    evalMCCSequence
      (g2Producer.counterAugment.initialMCCWithMem 0
        (initialMem g2Producer.arrayLen 0))
      g2Producer.rolledCompile = some g2ProducerOut ∧
    g2ProducerOut.env ⟨g2Producer.output + 1⟩ = some (0 : Int) ∧
    Option.bind
      (evalMCCSequence
        (g2Scanner.counterAugment.initialMCCWithMem 0 g2ProducerOut.mem)
        g2Scanner.rolledCompile)
      (fun m : MCCState => m.env ⟨g2Scanner.output + 1⟩) = some (0 : Int)

/-- The physical receipt identifies successful zero source runs over the two
symbolic producer tables. -/
theorem source_runs (h : Receipt) :
    let table1 := LeanCompCert.Ports.Section413G1TableProgram.rawFinal
      g1TableCfg
    let table2 := LeanCompCert.Ports.Section413G2TableProgram.rawFinal
      g2TableCfg
    (table1.regs LeanCompCert.Ports.Section413G1Program.rViol = 0 ∧
      ∃ out, g1Scanner.runFromArray table1.arr = some out ∧
        out.regs g1Scanner.output = 0) ∧
    (table2.regs LeanCompCert.Ports.Section413G2Program.rViol = 0 ∧
      ∃ out, g2Scanner.runFromArray table2.arr = some out ∧
        out.regs g2Scanner.output = 0) := by
  dsimp only
  rcases h with ⟨g1Out, g2Out, h1run, h1zero, h1scan,
    h2run, h2zero, h2scan⟩
  have hBase1Producer : BaseOk g1Producer.arrayLen 0 := by
    change 0 ≤ (0 : Int) ∧
      (0 : Int) + ((8 * 500000 : Nat) : Int) ≤ ((M : Nat) : Int)
    decide
  have hBase1Scanner : BaseOk g1Scanner.arrayLen 0 := by
    change 0 ≤ (0 : Int) ∧
      (0 : Int) + ((8 * 500000 : Nat) : Int) ≤ ((M : Nat) : Int)
    decide
  have hBase2Producer : BaseOk g2Producer.arrayLen 0 := by
    change 0 ≤ (0 : Int) ∧
      (0 : Int) + ((8 * 500000 : Nat) : Int) ≤ ((M : Nat) : Int)
    decide
  have hBase2Scanner : BaseOk g2Scanner.arrayLen 0 := by
    change 0 ≤ (0 : Int) ∧
      (0 : Int) + ((8 * 500000 : Nat) : Int) ≤ ((M : Nat) : Int)
    decide
  constructor
  · apply g1_pipeline_zero_sound 0 (initialMem g1Producer.arrayLen 0)
      g1Out hBase1Producer hBase1Scanner
    · intro k hk
      exact initialMem_cell g1Producer.arrayLen 0 hk
    · exact h1run
    · exact h1zero
    · exact h1scan
  · apply g2_pipeline_zero_sound 0 (initialMem g2Producer.arrayLen 0)
      g2Out hBase2Producer hBase2Scanner
    · intro k hk
      exact initialMem_cell g2Producer.arrayLen 0 hk
    · exact h2run
    · exact h2zero
    · exact h2scan

/-- All per-event arithmetic receipts and enabled paper bounds follow from
the compact physical receipt by uniform symbolic induction.  Applying this
theorem at the production constants does not evaluate either scanner fold.
-/
theorem event_receipts_and_bounds (h : Receipt) :
    let table1 := LeanCompCert.Ports.Section413G1TableProgram.rawFinal
      g1TableCfg
    let entry1 := arun 0 (initialAStateWithArray table1.arr)
      LeanCompCert.Ports.Section413WindowEventScanner.init
    let table2 := LeanCompCert.Ports.Section413G2TableProgram.rawFinal
      g2TableCfg
    let entry2 := arun 0 (initialAStateWithArray table2.arr)
      LeanCompCert.Ports.Section413WindowEventScanner.init
    (∀ k, k < LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg.rows *
        LeanCompCert.Ports.Section413WindowSchedule.slots →
      LeanCompCert.Ports.Section413WindowEventScanner.EventBodyReceipts k
          (LeanCompCert.Ports.Section413WindowEventScanner.scheduledState k
            (LeanCompCert.Ports.Section413WindowEventScanner.scannerStateAt
              LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg entry1 k))
          LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg ∧
        (LeanCompCert.Ports.Section413WindowEventScanner.checkedSlot
            LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg k →
          LeanCompCert.Ports.Section413WindowEventScanner.paperBoundAt
            LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg k
            (LeanCompCert.Ports.Section413WindowEventScanner.scannerStateAt
              LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg entry1 k))) ∧
    (∀ k, k < LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg.rows *
        LeanCompCert.Ports.Section413WindowSchedule.slots →
      LeanCompCert.Ports.Section413WindowEventScanner.EventBodyReceipts k
          (LeanCompCert.Ports.Section413WindowEventScanner.scheduledState k
            (LeanCompCert.Ports.Section413WindowEventScanner.scannerStateAt
              LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg entry2 k))
          LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg ∧
        (LeanCompCert.Ports.Section413WindowEventScanner.checkedSlot
            LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg k →
          LeanCompCert.Ports.Section413WindowEventScanner.paperBoundAt
            LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg k
            (LeanCompCert.Ports.Section413WindowEventScanner.scannerStateAt
              LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg entry2 k))) := by
  dsimp only
  obtain ⟨⟨_, out1, hrun1, hzero1⟩, ⟨_, out2, hrun2, hzero2⟩⟩ :=
    source_runs h
  have harray1 : ∀ j,
      (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr j <
        M := by
    rw [LeanCompCert.Ports.Section413G1TableSound.rawFinal_eq_prefix]
    exact (LeanCompCert.Ports.Section413G1TableSound.rawPrefix_wordInv
      g1TableCfg g1TableCfg_admissible g1TableCfg.loopCount
        (Nat.le_refl _)).2
  have harray2 : ∀ j,
      (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr j <
        M := by
    rw [LeanCompCert.Ports.Section413G2TableSound.rawFinal_eq_prefix]
    exact (LeanCompCert.Ports.Section413G2TableSound.rawPrefix_wordInv
      g2TableCfg g2TableCfg_admissible g2TableCfg.loopCount
        (Nat.le_refl _)).2
  constructor
  · apply
      LeanCompCert.Ports.Section413WindowEventScanner.program_runFromArray_zero_implies_receipts_and_bounds
        LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg
        (LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg).arr
        harray1 (by decide) (by decide) (by decide) (by decide) (by decide)
        LeanCompCert.Ports.Section413WindowEventScanner.g1EventDefinedFrames
        LeanCompCert.Ports.Section413WindowEventScanner.g1EventBodyFrames
        (by decide) (by decide) out1
    · simpa only [g1Scanner] using hrun1
    · simpa only [g1Scanner] using hzero1
  · apply
      LeanCompCert.Ports.Section413WindowEventScanner.program_runFromArray_zero_implies_receipts_and_bounds
        LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg
        (LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg).arr
        harray2 (by decide) (by decide) (by decide) (by decide) (by decide)
        LeanCompCert.Ports.Section413WindowEventScanner.g2EventDefinedFrames
        LeanCompCert.Ports.Section413WindowEventScanner.g2EventBodyFrames
        (by decide) (by decide) out2
    · simpa only [g2Scanner] using hrun2
    · simpa only [g2Scanner] using hzero2

#print axioms source_runs
#print axioms event_receipts_and_bounds

end LeanCompCert.Ports.Section413Window99999PipelineReceipt

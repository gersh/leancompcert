import LeanCompCert.Ports.Section413G1TableProducer
import LeanCompCert.Ports.Section413G2TableProducer
import LeanCompCert.Ports.Section413WindowScannerFoldSound

/-!
# Shared-memory soundness of the Section 4.1.3 compiled pipelines

The physical artifact calls a rolled table producer and a rolled scanner on
the same array.  These theorems identify that caller-owned memory with the
producer's symbolic final array, then read the scanner's compact zero receipt
back as the symbolic scanner flag.  No production loop or table is evaluated
by Lean.
-/

namespace LeanCompCert.Ports.Section413WindowPipelineSound

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.ArrayFoldBridge

def g1TableCfg : LeanCompCert.Ports.Section413G1Program.Cfg :=
  ⟨99999, 999, 33⟩

def g2TableCfg : LeanCompCert.Ports.Section413G2Program.Cfg :=
  ⟨99999, 999, 33⟩

theorem g1TableCfg_sound :
    LeanCompCert.Ports.Section413G1Sound.Admissible g1TableCfg :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem g1TableCfg_admissible :
    LeanCompCert.Ports.Section413G1TableProgram.TableAdmissible g1TableCfg :=
  ⟨g1TableCfg_sound.toDenote, by decide⟩

theorem g2TableCfg_sound :
    LeanCompCert.Ports.Section413G2Sound.Admissible g2TableCfg :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

theorem g2TableCfg_admissible :
    LeanCompCert.Ports.Section413G2TableProgram.TableAdmissible g2TableCfg :=
  ⟨g2TableCfg_sound.toDenote, by decide⟩

def g1Producer : AProgram :=
  LeanCompCert.Ports.Section413G1TableProducer.producerProgram g1TableCfg

def g2Producer : AProgram :=
  LeanCompCert.Ports.Section413G2TableProducer.producerProgram g2TableCfg

def g1Scanner : AProgram :=
  LeanCompCert.Ports.Section413WindowEventScanner.program
    LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg

def g2Scanner : AProgram :=
  LeanCompCert.Ports.Section413WindowEventScanner.program
    LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg

set_option maxRecDepth 10000 in
/-- The exact G1 producer-to-scanner physical trace yields two symbolic clean
flags over the producer's table array. -/
theorem g1_pipeline_zero_sound (base : Int) (mem : Mem) (producerOut : MCCState)
    (hProducerBase : BaseOk g1Producer.arrayLen base)
    (hScannerBase : BaseOk g1Scanner.arrayLen base)
    (hZeroCells : ∀ k, k < g1Producer.arrayLen →
      mem (cellAddr base k) = some (0 : Int))
    (hProducerRun : evalMCCSequence
      (g1Producer.counterAugment.initialMCCWithMem base mem)
      g1Producer.rolledCompile = some producerOut)
    (hProducerReceipt :
      producerOut.env ⟨g1Producer.output + 1⟩ = some (0 : Int))
    (hScannerReceipt : Option.bind
      (evalMCCSequence
        (g1Scanner.counterAugment.initialMCCWithMem base producerOut.mem)
        g1Scanner.rolledCompile)
      (fun m : MCCState => m.env ⟨g1Scanner.output + 1⟩) = some (0 : Int)) :
    let table := LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg
    table.regs LeanCompCert.Ports.Section413G1Program.rViol = 0 ∧
      ∃ out, g1Scanner.runFromArray table.arr = some out ∧
        out.regs g1Scanner.output = 0 := by
  dsimp only
  generalize htableDef :
    LeanCompCert.Ports.Section413G1TableProgram.rawFinal g1TableCfg = table
  have hSourceRun : g1Producer.runFromArray (fun _ => 0) = some table := by
    have h := LeanCompCert.Ports.Section413G1TableProducer.producer_runFromZero
      g1TableCfg g1TableCfg_admissible
    rw [htableDef] at h
    simpa only [g1Producer] using h
  obtain ⟨augOut, hAugRun, hAgree⟩ :=
    g1Producer.counterAugment_runFromArray_of_runFromArray
      (LeanCompCert.Ports.Section413G1TableProducer.producerProgram_wf _)
      (fun _ => 0) table hSourceRun
  obtain ⟨machineOut, hMachineRun, hRel⟩ :=
    g1Producer.evalCC_rolledCompile_fromArray
      (LeanCompCert.Ports.Section413G1TableProducer.producerProgram_wf _)
      base hProducerBase (fun _ => 0) mem hZeroCells
      (fun _ _ => by decide) augOut hAugRun
  have hm : machineOut = producerOut := by
    rw [hProducerRun] at hMachineRun
    exact (Option.some.inj hMachineRun).symm
  subst machineOut
  have hTableAgree := hRel.hregs.1
    LeanCompCert.Ports.Section413G1Program.rViol (by decide)
  have hTableZero : table.regs LeanCompCert.Ports.Section413G1Program.rViol = 0 := by
    have hAugZero : augOut.regs LeanCompCert.Ports.Section413G1Program.rViol = 0 := by
      have hProducerReceipt' : producerOut.env
          ⟨LeanCompCert.Ports.Section413G1Program.rViol + 1⟩ = some (0 : Int) := by
        simpa only [g1Producer,
          LeanCompCert.Ports.Section413G1TableProducer.producerProgram] using
          hProducerReceipt
      rw [hProducerReceipt'] at hTableAgree
      exact_mod_cast Option.some.inj hTableAgree.symm
    exact (hAgree.1 LeanCompCert.Ports.Section413G1Program.rViol
      (by decide)).trans hAugZero
  have hLen : g1Scanner.arrayLen ≤ g1Producer.arrayLen := by decide
  have hScannerCells : ∀ k, k < g1Scanner.arrayLen →
      producerOut.mem (cellAddr base k) = some ((table.arr k : Nat) : Int) := by
    intro k hk
    rw [hAgree.2]
    exact hRel.hcells k (Nat.lt_of_lt_of_le hk hLen)
  have hScannerCellsLt : ∀ k, k < g1Scanner.arrayLen → table.arr k < M := by
    intro k hk
    rw [hAgree.2]
    exact hRel.hcellsLt k (Nat.lt_of_lt_of_le hk hLen)
  let entry := arun 0 (initialAStateWithArray table.arr)
    LeanCompCert.Ports.Section413WindowEventScanner.init
  let scanOut := arun 0
    (LeanCompCert.Ports.Section413WindowEventScanner.scannerStateAt
      LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg entry
      (LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg.rows *
        LeanCompCert.Ports.Section413WindowSchedule.slots))
    LeanCompCert.Ports.Section413WindowEventScanner.epilogue
  have hScannerRun : g1Scanner.runFromArray table.arr = some scanOut := by
    simpa only [g1Scanner, entry, scanOut] using
      LeanCompCert.Ports.Section413WindowEventScanner.program_runFromArray
        LeanCompCert.Ports.Section413WindowEventScanner.g1Cfg table.arr
        (by decide) (by decide) (by decide) (by decide) (by decide)
        LeanCompCert.Ports.Section413WindowEventScanner.g1EventDefinedFrames
        LeanCompCert.Ports.Section413WindowEventScanner.g1EventBodyFrames
  have hScannerZero : scanOut.regs g1Scanner.output = 0 := by
    exact AProgram.output_eq_of_rolledCompile_fromArray g1Scanner
      LeanCompCert.Ports.Section413WindowEventScanner.g1Program_wf base
      hScannerBase table.arr producerOut.mem hScannerCells hScannerCellsLt
      scanOut hScannerRun 0 hScannerReceipt
  constructor
  · exact hTableZero
  · exact ⟨scanOut, hScannerRun, hScannerZero⟩

set_option maxRecDepth 10000 in
/-- G2 counterpart of `g1_pipeline_zero_sound`. -/
theorem g2_pipeline_zero_sound (base : Int) (mem : Mem) (producerOut : MCCState)
    (hProducerBase : BaseOk g2Producer.arrayLen base)
    (hScannerBase : BaseOk g2Scanner.arrayLen base)
    (hZeroCells : ∀ k, k < g2Producer.arrayLen →
      mem (cellAddr base k) = some (0 : Int))
    (hProducerRun : evalMCCSequence
      (g2Producer.counterAugment.initialMCCWithMem base mem)
      g2Producer.rolledCompile = some producerOut)
    (hProducerReceipt :
      producerOut.env ⟨g2Producer.output + 1⟩ = some (0 : Int))
    (hScannerReceipt : Option.bind
      (evalMCCSequence
        (g2Scanner.counterAugment.initialMCCWithMem base producerOut.mem)
        g2Scanner.rolledCompile)
      (fun m : MCCState => m.env ⟨g2Scanner.output + 1⟩) = some (0 : Int)) :
    let table := LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg
    table.regs LeanCompCert.Ports.Section413G2Program.rViol = 0 ∧
      ∃ out, g2Scanner.runFromArray table.arr = some out ∧
        out.regs g2Scanner.output = 0 := by
  dsimp only
  generalize htableDef :
    LeanCompCert.Ports.Section413G2TableProgram.rawFinal g2TableCfg = table
  have hSourceRun : g2Producer.runFromArray (fun _ => 0) = some table := by
    have h := LeanCompCert.Ports.Section413G2TableProducer.producer_runFromZero
      g2TableCfg g2TableCfg_admissible
    rw [htableDef] at h
    simpa only [g2Producer] using h
  obtain ⟨augOut, hAugRun, hAgree⟩ :=
    g2Producer.counterAugment_runFromArray_of_runFromArray
      (LeanCompCert.Ports.Section413G2TableProducer.producerProgram_wf _)
      (fun _ => 0) table hSourceRun
  obtain ⟨machineOut, hMachineRun, hRel⟩ :=
    g2Producer.evalCC_rolledCompile_fromArray
      (LeanCompCert.Ports.Section413G2TableProducer.producerProgram_wf _)
      base hProducerBase (fun _ => 0) mem hZeroCells
      (fun _ _ => by decide) augOut hAugRun
  have hm : machineOut = producerOut := by
    rw [hProducerRun] at hMachineRun
    exact (Option.some.inj hMachineRun).symm
  subst machineOut
  have hTableAgree := hRel.hregs.1
    LeanCompCert.Ports.Section413G2Program.rViol (by decide)
  have hTableZero : table.regs LeanCompCert.Ports.Section413G2Program.rViol = 0 := by
    have hAugZero : augOut.regs LeanCompCert.Ports.Section413G2Program.rViol = 0 := by
      have hProducerReceipt' : producerOut.env
          ⟨LeanCompCert.Ports.Section413G2Program.rViol + 1⟩ = some (0 : Int) := by
        simpa only [g2Producer,
          LeanCompCert.Ports.Section413G2TableProducer.producerProgram] using
          hProducerReceipt
      rw [hProducerReceipt'] at hTableAgree
      exact_mod_cast Option.some.inj hTableAgree.symm
    exact (hAgree.1 LeanCompCert.Ports.Section413G2Program.rViol
      (by decide)).trans hAugZero
  have hLen : g2Scanner.arrayLen ≤ g2Producer.arrayLen := by decide
  have hScannerCells : ∀ k, k < g2Scanner.arrayLen →
      producerOut.mem (cellAddr base k) = some ((table.arr k : Nat) : Int) := by
    intro k hk
    rw [hAgree.2]
    exact hRel.hcells k (Nat.lt_of_lt_of_le hk hLen)
  have hScannerCellsLt : ∀ k, k < g2Scanner.arrayLen → table.arr k < M := by
    intro k hk
    rw [hAgree.2]
    exact hRel.hcellsLt k (Nat.lt_of_lt_of_le hk hLen)
  let entry := arun 0 (initialAStateWithArray table.arr)
    LeanCompCert.Ports.Section413WindowEventScanner.init
  let scanOut := arun 0
    (LeanCompCert.Ports.Section413WindowEventScanner.scannerStateAt
      LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg entry
      (LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg.rows *
        LeanCompCert.Ports.Section413WindowSchedule.slots))
    LeanCompCert.Ports.Section413WindowEventScanner.epilogue
  have hScannerRun : g2Scanner.runFromArray table.arr = some scanOut := by
    simpa only [g2Scanner, entry, scanOut] using
      LeanCompCert.Ports.Section413WindowEventScanner.program_runFromArray
        LeanCompCert.Ports.Section413WindowEventScanner.g2Cfg table.arr
        (by decide) (by decide) (by decide) (by decide) (by decide)
        LeanCompCert.Ports.Section413WindowEventScanner.g2EventDefinedFrames
        LeanCompCert.Ports.Section413WindowEventScanner.g2EventBodyFrames
  have hScannerZero : scanOut.regs g2Scanner.output = 0 := by
    exact AProgram.output_eq_of_rolledCompile_fromArray g2Scanner
      LeanCompCert.Ports.Section413WindowEventScanner.g2Program_wf base
      hScannerBase table.arr producerOut.mem hScannerCells hScannerCellsLt
      scanOut hScannerRun 0 hScannerReceipt
  exact ⟨hTableZero, ⟨scanOut, hScannerRun, hScannerZero⟩⟩

#print axioms g1TableCfg_admissible
#print axioms g2TableCfg_admissible
#print axioms g1_pipeline_zero_sound
#print axioms g2_pipeline_zero_sound

end LeanCompCert.Ports.Section413WindowPipelineSound

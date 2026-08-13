/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowScannerStepSound
import LeanCompCert.Verified.ArrayPipeline
import LeanCompCert.Verified.ArrayRolledPipeline

/-!
# Symbolic fold of the compiled Section 4.1.3 scanner

The production iteration count remains beneath `List.range`; no theorem in
this file reduces that range.  The induction is uniform in the prefix length.
-/

namespace LeanCompCert.Ports.Section413WindowEventScanner

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.Section413Cells

def scannerStateAt (c : Cfg) (entry : AState) (n : Nat) : AState :=
  (List.range n).foldl (fun s k => arun k s (body c)) entry

def checkedSlot (c : Cfg) (k : Nat) : Prop :=
  (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).s =
      LeanCompCert.Ports.Section413WindowSchedule.slots ∧
    c.checkLo ≤ (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).n

def paperUpperAt (c : Cfg) (k : Nat) (s : AState) : Nat :=
  let e := eventedState k s c
  let n := (LeanCompCert.Ports.Section413WindowSchedule.slotAt k).n
  let hiN := -((-decodeZ (e.regs
    LeanCompCert.Ports.Section413WindowRowCheck.rK2Hi)) / (n : Int))
  let hiNext := -((-decodeZ (e.regs
    LeanCompCert.Ports.Section413WindowRowCheck.rK2Hi)) /
      ((n + 1 : Nat) : Int))
  ((if hiN ≥ hiNext then hiN else hiNext) +
    decodeZ (e.regs LeanCompCert.Ports.Section413WindowRowCheck.rK1Hi)).toNat

def paperBoundAt (c : Cfg) (k : Nat) (s : AState) : Prop :=
  paperUpperAt c k s ≤
    LeanCompCert.Ports.Section413WindowRowCheck.commonBound - c.offset

@[simp] theorem scannerStateAt_zero (c : Cfg) (entry : AState) :
    scannerStateAt c entry 0 = entry := rfl

theorem scannerStateAt_succ (c : Cfg) (entry : AState) (n : Nat) :
    scannerStateAt c entry (n + 1) =
      arun n (scannerStateAt c entry n) (body c) := by
  simp [scannerStateAt, List.range_succ, List.foldl_append]

theorem scannerStateAt_word (c : Cfg) (entry : AState)
    (hword : ∀ j, entry.regs j < M) (harray : ∀ j, entry.arr j < M) :
    ∀ n,
      (∀ j, (scannerStateAt c entry n).regs j < M) ∧
      (∀ j, (scannerStateAt c entry n).arr j < M) := by
  intro n
  induction n with
  | zero => exact ⟨hword, harray⟩
  | succ n ih =>
      rw [scannerStateAt_succ]
      exact arun_word n (body c) (scannerStateAt c entry n) ih.1 ih.2

/-- Source execution of the scanner from a caller-provided producer table.
The proof is a uniform fold induction through `runFromArray_eq_foldl_mem`;
the concrete production range remains opaque to Lean. -/
theorem program_runFromArray (c : Cfg) (arr : Nat → Nat)
    (hrows : c.rows ≤
      LeanCompCert.Ports.Section413WindowSchedule.productionRows)
    (hrowsCap : LeanCompCert.Ports.Section413WindowSchedule.productionRows ≤
      c.cap)
    (hslotsCap : LeanCompCert.Ports.Section413WindowSchedule.slots ≤ c.cap)
    (hcapH : c.cap < LeanCompCert.Ports.Section413Cells.H63)
    (htable : LeanCompCert.Ports.Section413WindowTableRead.tableLen c.cap < M)
    (hdefFrames : EventDefinedFrames c) (hbodyFrames : EventBodyFrames c) :
    let entry := arun 0 (initialAStateWithArray arr) init
    (program c).runFromArray arr = some
      (arun 0 (scannerStateAt c entry
        (c.rows * LeanCompCert.Ports.Section413WindowSchedule.slots))
        epilogue) := by
  dsimp only
  let entry := arun 0 (initialAStateWithArray arr) init
  apply AProgram.runFromArray_eq_foldl_mem
    (p := program c) (P := fun _ => True)
    (step := fun index s => arun index s (body c))
    (fin := fun s => arun 0 s epilogue) (arr := arr) (s₀ := entry)
  · apply denoteAInstrs_eq_arun
    have hi : AllDefined
        (LeanCompCert.Ports.Section413WindowTableRead.tableLen c.cap) 0
        (initialAStateWithArray arr) init := by
      rw [init, AllDefined_append]
      exact ⟨allDefined_lift_of_noDiv _ 0 _ _
          (by simp [eventInit, NoDivI]),
        allDefined_lift_of_noDiv _ 0 _ _
          (by simp [LeanCompCert.Ports.Section413WindowRowCheck.init,
            NoDivI])⟩
    simpa only [program] using hi
  · trivial
  · intro index s hindex _
    apply denoteAInstrs_eq_arun
    apply scannerBody_defined index s c
    · have htotal : c.rows *
          LeanCompCert.Ports.Section413WindowSchedule.slots ≤
          LeanCompCert.Ports.Section413WindowSchedule.productionRows *
            LeanCompCert.Ports.Section413WindowSchedule.slots :=
        Nat.mul_le_mul_right _ hrows
      exact Nat.lt_of_lt_of_le hindex htotal
    · exact hrowsCap
    · exact hslotsCap
    · exact hcapH
    · exact htable
    · exact hdefFrames
    · exact hbodyFrames
  · intros
    trivial
  · intro s _
    apply denoteAInstrs_eq_arun
    exact allDefined_lift_of_noDiv _ 0
      [ .binop rCombinedViol .bor
          (.reg LeanCompCert.Ports.Section413SignedAdd.rViol)
          (.reg LeanCompCert.Ports.Section413SignedScale.rViol)
      , .binop rCombinedViol .bor (.reg rCombinedViol)
          (.reg LeanCompCert.Ports.Section413WindowRowCheck.rRowViol) ] s
      (by simp [NoDivI])

/-- A compact word returned by the rolled CompCert scanner equals the output
of the symbolic source fold.  Runtime does the large computation; Lean only
uses compiler simulation and the uniform success theorem above. -/
theorem program_rolled_output_eq (c : Cfg) (hWF : (program c).WF)
    (arr : Nat → Nat) (base : Int) (mem : Verified.MemFragment.Mem)
    (hBase : BaseOk (program c).arrayLen base)
    (hCells : ∀ k, k < (program c).arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < (program c).arrayLen → arr k < M)
    (hrows : c.rows ≤
      LeanCompCert.Ports.Section413WindowSchedule.productionRows)
    (hrowsCap : LeanCompCert.Ports.Section413WindowSchedule.productionRows ≤
      c.cap)
    (hslotsCap : LeanCompCert.Ports.Section413WindowSchedule.slots ≤ c.cap)
    (hcapH : c.cap < LeanCompCert.Ports.Section413Cells.H63)
    (htable : LeanCompCert.Ports.Section413WindowTableRead.tableLen c.cap < M)
    (hdefFrames : EventDefinedFrames c) (hbodyFrames : EventBodyFrames c)
    (value : Nat)
    (hReceipt : Option.bind
      (Verified.MemFragment.evalMCCSequence
        ((program c).counterAugment.initialMCCWithMem base mem)
        (program c).rolledCompile)
      (fun m : Verified.MemFragment.MCCState =>
        m.env ⟨(program c).output + 1⟩) = some ((value : Nat) : Int)) :
    let entry := arun 0 (initialAStateWithArray arr) init
    (arun 0 (scannerStateAt c entry
      (c.rows * LeanCompCert.Ports.Section413WindowSchedule.slots)) epilogue).regs
        rCombinedViol = value := by
  dsimp only
  let entry := arun 0 (initialAStateWithArray arr) init
  let out := arun 0 (scannerStateAt c entry
    (c.rows * LeanCompCert.Ports.Section413WindowSchedule.slots)) epilogue
  have hrun : (program c).runFromArray arr = some out := by
    simpa only [entry, out] using program_runFromArray c arr hrows hrowsCap
      hslotsCap hcapH htable hdefFrames hbodyFrames
  have h := AProgram.output_eq_of_rolledCompile_fromArray (program c) hWF
    base hBase arr mem hCells hCellsLt out hrun value hReceipt
  simpa only [program, out] using h

/-- A zero compiled epilogue result splits into the three sticky flags read
by the program. -/
theorem epilogue_zero_implies_flags (k : Nat) (s : AState)
    (hword : ∀ j, s.regs j < M)
    (hzero : (arun k s epilogue).regs rCombinedViol = 0) :
    s.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
      s.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0 ∧
      s.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 := by
  have horAS : s.regs LeanCompCert.Ports.Section413SignedAdd.rViol |||
      s.regs LeanCompCert.Ports.Section413SignedScale.rViol < M :=
    LeanCompCert.Ports.Section413G1Denote.lor_lt_M (hword _) (hword _)
  have horAll :
      (s.regs LeanCompCert.Ports.Section413SignedAdd.rViol |||
        s.regs LeanCompCert.Ports.Section413SignedScale.rViol) |||
        s.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol < M :=
    LeanCompCert.Ports.Section413G1Denote.lor_lt_M horAS (hword _)
  have h :
      (s.regs LeanCompCert.Ports.Section413SignedAdd.rViol |||
        s.regs LeanCompCert.Ports.Section413SignedScale.rViol) |||
          s.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 := by
    have hzero' := hzero
    rw [epilogue, arun_lift] at hzero'
    simp [srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
      rCombinedViol, LeanCompCert.Ports.Section413WindowRowCheck.rRowViol,
      Nat.mod_eq_of_lt horAS] at hzero'
    have horAll' :
        (s.regs LeanCompCert.Ports.Section413SignedAdd.rViol |||
          s.regs LeanCompCert.Ports.Section413SignedScale.rViol) |||
          s.regs 73 < M := by
      simpa only [LeanCompCert.Ports.Section413WindowRowCheck.rRowViol]
        using horAll
    rw [Nat.mod_eq_of_lt horAll'] at hzero'
    simpa only [LeanCompCert.Ports.Section413WindowRowCheck.rRowViol]
      using hzero'
  have hall := LeanCompCert.Ports.Section413G1Sound.or_eq_zero h
  have harith := LeanCompCert.Ports.Section413G1Sound.or_eq_zero hall.1
  exact ⟨harith.1, harith.2, hall.2⟩

/-- A clean final row flag is equivalent to every enabled paper-shaped
upper bound in the prefix.  `hreceipts` contains only the two checked-add
bits for enabled final slots.  The theorem is uniform in `n`, so applying it
at the production count does not execute the production fold in Lean. -/
theorem scannerStateAt_zero_iff_bounds (c : Cfg) (entry : AState)
    (hword : ∀ j, entry.regs j < M) (harray : ∀ j, entry.arr j < M)
    (hf : EventBodyFrames c)
    (hlo : c.checkLo < M)
    (hlimit : LeanCompCert.Ports.Section413WindowRowCheck.commonBound -
      c.offset < M) :
    ∀ n,
      n ≤ LeanCompCert.Ports.Section413WindowSchedule.productionRows *
        LeanCompCert.Ports.Section413WindowSchedule.slots →
      (∀ k, k < n → checkedSlot c k →
        LeanCompCert.Ports.Section413WindowRowCheck.UnitReceipts k
          (LeanCompCert.Ports.Section413WindowRowCheck.bodyDivState k
            (eventedState k (scannerStateAt c entry k) c))) →
      ((scannerStateAt c entry n).regs
          LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 ↔
        entry.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 ∧
          ∀ k, k < n → checkedSlot c k →
            paperBoundAt c k (scannerStateAt c entry k)) := by
  intro n hn hreceipts
  induction n with
  | zero => simp
  | succ n ih =>
      have hnTotal : n <
          LeanCompCert.Ports.Section413WindowSchedule.productionRows *
            LeanCompCert.Ports.Section413WindowSchedule.slots := by omega
      have hsword := scannerStateAt_word c entry hword harray n
      have ih' := ih (by omega) (fun k hk hchecked =>
        hreceipts k (by omega) hchecked)
      rw [scannerStateAt_succ]
      constructor
      · intro hout
        have hprev := body_zero_implies_input_zero n
          (scannerStateAt c entry n) c hsword.1 hsword.2 hf hlo hlimit hout
        have hprefix := ih'.mp hprev
        refine ⟨hprefix.1, ?_⟩
        intro k hk hchecked
        by_cases hkn : k = n
        · subst k
          have hstep := body_zero_iff_paper_upper n
            (scannerStateAt c entry n) c hsword.1 hsword.2 hnTotal hf hlo
              hlimit hchecked.1 hchecked.2 hprev
              (hreceipts n (by omega) hchecked)
          exact hstep.mp hout
        · exact hprefix.2 k (by omega) hchecked
      · intro hall
        have hprefix : (scannerStateAt c entry n).regs
            LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 := by
          apply ih'.mpr
          exact ⟨hall.1, fun k hk hchecked => hall.2 k (by omega) hchecked⟩
        by_cases hchecked : checkedSlot c n
        · have hstep := body_zero_iff_paper_upper n
            (scannerStateAt c entry n) c hsword.1 hsword.2 hnTotal hf hlo
              hlimit hchecked.1 hchecked.2 hprefix
              (hreceipts n (by omega) hchecked)
          apply hstep.mpr
          exact hall.2 n (by omega) hchecked
        · have hskip :
              (LeanCompCert.Ports.Section413WindowSchedule.slotAt n).s ≠
                  LeanCompCert.Ports.Section413WindowSchedule.slots ∨
                (LeanCompCert.Ports.Section413WindowSchedule.slotAt n).n <
                  c.checkLo := by
            by_cases hs :
                (LeanCompCert.Ports.Section413WindowSchedule.slotAt n).s =
                  LeanCompCert.Ports.Section413WindowSchedule.slots
            · right
              have hnlo : ¬ c.checkLo ≤
                  (LeanCompCert.Ports.Section413WindowSchedule.slotAt n).n :=
                fun hpast => hchecked ⟨hs, hpast⟩
              omega
            · exact Or.inl hs
          rw [body_unchecked_row n (scannerStateAt c entry n) c
            hsword.1 hsword.2 hnTotal hf hlo hlimit hskip]
          exact hprefix

/-- Receipt-facing fold theorem.  A clean final row flag and checked-add flag
from the compiled scan imply every enabled paper bound in the prefix.  The
induction is symbolic in `n`; no concrete production range is reduced. -/
theorem scannerStateAt_flags_zero_implies_bounds (c : Cfg) (entry : AState)
    (hword : ∀ j, entry.regs j < M) (harray : ∀ j, entry.arr j < M)
    (hf : EventBodyFrames c)
    (hlo : c.checkLo < M)
    (hlimit : LeanCompCert.Ports.Section413WindowRowCheck.commonBound -
      c.offset < M) :
    ∀ n,
      n ≤ LeanCompCert.Ports.Section413WindowSchedule.productionRows *
        LeanCompCert.Ports.Section413WindowSchedule.slots →
      (scannerStateAt c entry n).regs
          LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 →
      (scannerStateAt c entry n).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0 →
      entry.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 ∧
        entry.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
          ∀ k, k < n → checkedSlot c k →
            paperBoundAt c k (scannerStateAt c entry k) := by
  intro n hn hrow hadd
  induction n with
  | zero => exact ⟨hrow, hadd, by simp⟩
  | succ n ih =>
      have hnTotal : n <
          LeanCompCert.Ports.Section413WindowSchedule.productionRows *
            LeanCompCert.Ports.Section413WindowSchedule.slots := by omega
      have hsword := scannerStateAt_word c entry hword harray n
      have hrowStep : (arun n (scannerStateAt c entry n) (body c)).regs
          LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 := by
        simpa only [scannerStateAt_succ] using hrow
      have haddStep : (arun n (scannerStateAt c entry n) (body c)).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
        simpa only [scannerStateAt_succ] using hadd
      have hrowPrev := body_zero_implies_input_zero n
        (scannerStateAt c entry n) c hsword.1 hsword.2 hf hlo hlimit hrowStep
      have haddPrev := body_add_zero_implies_input_zero n
        (scannerStateAt c entry n) c hsword.1 hsword.2 hlo hlimit haddStep
      have hprefix := ih (by omega) hrowPrev haddPrev
      refine ⟨hprefix.1, hprefix.2.1, ?_⟩
      intro k hk hchecked
      by_cases hkn : k = n
      · subst k
        exact body_flags_zero_implies_paper_upper n
          (scannerStateAt c entry n) c hsword.1 hsword.2 hnTotal hf hlo
            hlimit hchecked.1 hchecked.2 hrowStep haddStep
      · exact hprefix.2.2 k (by omega) hchecked

/-- Full receipt-facing symbolic fold.  The three final compiled flags imply
the receipt bundle for every executed event body and every enabled paper
bound.  The abstract prefix length is never evaluated in Lean. -/
theorem scannerStateAt_flags_zero_implies_receipts_and_bounds
    (c : Cfg) (entry : AState)
    (hword : ∀ j, entry.regs j < M) (harray : ∀ j, entry.arr j < M)
    (hf : EventBodyFrames c)
    (hlo : c.checkLo < M)
    (hlimit : LeanCompCert.Ports.Section413WindowRowCheck.commonBound -
      c.offset < M) :
    ∀ n,
      n ≤ LeanCompCert.Ports.Section413WindowSchedule.productionRows *
        LeanCompCert.Ports.Section413WindowSchedule.slots →
      (scannerStateAt c entry n).regs
          LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 →
      (scannerStateAt c entry n).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0 →
      (scannerStateAt c entry n).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0 →
      entry.regs LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 ∧
        entry.regs LeanCompCert.Ports.Section413SignedScale.rViol = 0 ∧
        entry.regs LeanCompCert.Ports.Section413SignedAdd.rViol = 0 ∧
          ∀ k, k < n →
            EventBodyReceipts k
                (scheduledState k (scannerStateAt c entry k)) c ∧
              (checkedSlot c k →
                paperBoundAt c k (scannerStateAt c entry k)) := by
  intro n hn hrow hscale hadd
  induction n with
  | zero => exact ⟨hrow, hscale, hadd, by simp⟩
  | succ n ih =>
      have hnTotal : n <
          LeanCompCert.Ports.Section413WindowSchedule.productionRows *
            LeanCompCert.Ports.Section413WindowSchedule.slots := by omega
      have hsword := scannerStateAt_word c entry hword harray n
      have hrowStep : (arun n (scannerStateAt c entry n) (body c)).regs
          LeanCompCert.Ports.Section413WindowRowCheck.rRowViol = 0 := by
        simpa only [scannerStateAt_succ] using hrow
      have hscaleStep : (arun n (scannerStateAt c entry n) (body c)).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0 := by
        simpa only [scannerStateAt_succ] using hscale
      have haddStep : (arun n (scannerStateAt c entry n) (body c)).regs
          LeanCompCert.Ports.Section413SignedAdd.rViol = 0 := by
        simpa only [scannerStateAt_succ] using hadd
      have hrowPrev := body_zero_implies_input_zero n
        (scannerStateAt c entry n) c hsword.1 hsword.2 hf hlo hlimit hrowStep
      have hreceipts := body_flags_zero_implies_event_receipts_and_input n
        (scannerStateAt c entry n) c hsword.1 hsword.2 hlo hlimit
          hscaleStep haddStep
      have hprefix := ih (by omega) hrowPrev hreceipts.2.1 hreceipts.2.2
      refine ⟨hprefix.1, hprefix.2.1, hprefix.2.2.1, ?_⟩
      intro k hk
      by_cases hkn : k = n
      · subst k
        refine ⟨hreceipts.1, ?_⟩
        intro hchecked
        exact body_flags_zero_implies_paper_upper n
          (scannerStateAt c entry n) c hsword.1 hsword.2 hnTotal hf hlo
            hlimit hchecked.1 hchecked.2 hrowStep haddStep
      · exact hprefix.2.2.2 k (by omega)

/-- A successful zero denotation of the compiled scanner program yields the
symbolic receipts and paper bounds.  This theorem consumes the run result; it
does not evaluate the concrete loop in Lean. -/
theorem program_denote_zero_implies_receipts_and_bounds (c : Cfg)
    (hrows : c.rows ≤
      LeanCompCert.Ports.Section413WindowSchedule.productionRows)
    (hf : EventBodyFrames c)
    (hlo : c.checkLo < M)
    (hlimit : LeanCompCert.Ports.Section413WindowRowCheck.commonBound -
      c.offset < M)
    (hrun : (program c).denote = some 0) :
    let entry := arun 0 initialAState init
    ∀ k, k < c.rows *
        LeanCompCert.Ports.Section413WindowSchedule.slots →
      EventBodyReceipts k (scheduledState k (scannerStateAt c entry k)) c ∧
        (checkedSlot c k → paperBoundAt c k (scannerStateAt c entry k)) := by
  dsimp only
  let entry := arun 0 initialAState init
  let total := c.rows *
    LeanCompCert.Ports.Section413WindowSchedule.slots
  have hinitialWord : ∀ j, initialAState.regs j < M := by
    intro j
    simp [initialAState, initialState, M]
  have hinitialArray : ∀ j, initialAState.arr j < M := by
    intro j
    simp [initialAState, M]
  have hentryWord : ∀ j, entry.regs j < M :=
    arun_regs_word 0 _ _ hinitialWord hinitialArray
  have hentryArray : ∀ j, entry.arr j < M :=
    arun_arr_word 0 _ _ hinitialWord hinitialArray
  have hrun' := AProgram.output_eq_arun_of_denote_eq_some (program c) hrun
  have hout : (arun 0 (scannerStateAt c entry total) epilogue).regs
      rCombinedViol = 0 := by
    simpa only [program, scannerStateAt, entry, total] using hrun'.symm
  have hfinalWord := scannerStateAt_word c entry hentryWord hentryArray total
  have hflags := epilogue_zero_implies_flags 0
    (scannerStateAt c entry total) hfinalWord.1 hout
  have hall := scannerStateAt_flags_zero_implies_receipts_and_bounds c entry
    hentryWord hentryArray hf hlo hlimit total (by
      dsimp only [total]
      exact Nat.mul_le_mul_right _ hrows) hflags.2.2
      hflags.2.1 hflags.1
  exact hall.2.2.2

/-- A successful source run from a caller-provided table, together with a
zero output receipt supplied by the rolled CompCert simulation, yields every
event receipt and enabled paper bound.  The production loop is related to the
uniform symbolic fold by `program_runFromArray`; it is never normalized here.
-/
theorem program_runFromArray_zero_implies_receipts_and_bounds (c : Cfg)
    (arr : Nat → Nat)
    (harray : ∀ j, arr j < M)
    (hrows : c.rows ≤
      LeanCompCert.Ports.Section413WindowSchedule.productionRows)
    (hrowsCap : LeanCompCert.Ports.Section413WindowSchedule.productionRows ≤
      c.cap)
    (hslotsCap : LeanCompCert.Ports.Section413WindowSchedule.slots ≤ c.cap)
    (hcapH : c.cap < LeanCompCert.Ports.Section413Cells.H63)
    (htable : LeanCompCert.Ports.Section413WindowTableRead.tableLen c.cap < M)
    (hdefFrames : EventDefinedFrames c) (hbodyFrames : EventBodyFrames c)
    (hlo : c.checkLo < M)
    (hlimit : LeanCompCert.Ports.Section413WindowRowCheck.commonBound -
      c.offset < M)
    (out : AState)
    (hrun : (program c).runFromArray arr = some out)
    (hzero : out.regs (program c).output = 0) :
    let entry := arun 0 (initialAStateWithArray arr) init
    ∀ k, k < c.rows *
        LeanCompCert.Ports.Section413WindowSchedule.slots →
      EventBodyReceipts k (scheduledState k (scannerStateAt c entry k)) c ∧
        (checkedSlot c k → paperBoundAt c k (scannerStateAt c entry k)) := by
  dsimp only
  let entry := arun 0 (initialAStateWithArray arr) init
  let total := c.rows *
    LeanCompCert.Ports.Section413WindowSchedule.slots
  let symbolicOut := arun 0 (scannerStateAt c entry total) epilogue
  have hinitialWord : ∀ j, (initialAStateWithArray arr).regs j < M := by
    intro j
    simp [initialAStateWithArray, initialState, M]
  have hinitialArray : ∀ j, (initialAStateWithArray arr).arr j < M := by
    intro j
    simpa only [initialAStateWithArray] using harray j
  have hentryWord : ∀ j, entry.regs j < M :=
    arun_regs_word 0 _ _ hinitialWord hinitialArray
  have hentryArray : ∀ j, entry.arr j < M :=
    arun_arr_word 0 _ _ hinitialWord hinitialArray
  have hsymbol : (program c).runFromArray arr = some symbolicOut := by
    simpa only [entry, total, symbolicOut] using
      program_runFromArray c arr hrows hrowsCap hslotsCap hcapH htable
        hdefFrames hbodyFrames
  have houtEq : out = symbolicOut := by
    rw [hrun] at hsymbol
    exact Option.some.inj hsymbol
  subst out
  have hout : symbolicOut.regs rCombinedViol = 0 := by
    simpa only [program] using hzero
  have hfinalWord := scannerStateAt_word c entry hentryWord hentryArray total
  have hflags := epilogue_zero_implies_flags 0
    (scannerStateAt c entry total) hfinalWord.1 (by
      simpa only [symbolicOut] using hout)
  have hall := scannerStateAt_flags_zero_implies_receipts_and_bounds c entry
    hentryWord hentryArray hbodyFrames hlo hlimit total (by
      dsimp only [total]
      exact Nat.mul_le_mul_right _ hrows) hflags.2.2 hflags.2.1 hflags.1
  exact hall.2.2.2

#print axioms scannerStateAt_word
#print axioms program_runFromArray
#print axioms program_rolled_output_eq
#print axioms epilogue_zero_implies_flags
#print axioms scannerStateAt_zero_iff_bounds
#print axioms scannerStateAt_flags_zero_implies_bounds
#print axioms scannerStateAt_flags_zero_implies_receipts_and_bounds
#print axioms program_denote_zero_implies_receipts_and_bounds
#print axioms program_runFromArray_zero_implies_receipts_and_bounds

end LeanCompCert.Ports.Section413WindowEventScanner

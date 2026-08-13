/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowScannerStepSound

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

#print axioms scannerStateAt_word
#print axioms epilogue_zero_implies_flags
#print axioms scannerStateAt_zero_iff_bounds
#print axioms scannerStateAt_flags_zero_implies_bounds
#print axioms scannerStateAt_flags_zero_implies_receipts_and_bounds
#print axioms program_denote_zero_implies_receipts_and_bounds

end LeanCompCert.Ports.Section413WindowEventScanner

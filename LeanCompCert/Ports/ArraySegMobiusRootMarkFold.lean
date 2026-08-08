import LeanCompCert.Ports.ArraySegMobiusScheduleFold

/-!
# Finite root-table marking fold

The root selector exposes only the bootstrap prefix of the growing prime
table.  This module generalizes the production cursor simulation from the
completed main table to an arbitrary represented prefix with an explicit,
positive terminal guard.  The guard is part of the representation because
the machine deliberately loads it when the cursor reaches the selected
limit.
-/

namespace LeanCompCert.Ports.ArraySegMobiusRootMarkFold

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusRootCellFold
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusCursorModel
open LeanCompCert.Ports.ArraySegMobiusScheduleFold
open LeanCompCert.Ports.ArraySegMobiusPrimeTable
open LeanCompCert.Ports.ArraySegMobiusPrimeTableRep
open LeanCompCert.Verified.PackedSieve

/-- Exact representation of the selected prime prefix and the cell loaded
when its cursor reaches the terminal limit. -/
structure LimitTableRep (c : Cfg) (s : AState) (ps : List Nat)
    (guard : Nat) : Prop where
  table : TablePrefix s.arr c.primeBase ps
  guard_eq : s.arr (c.primeBase + ps.length) = guard
  guard_pos : 0 < guard
  guard_lt_modulus : guard < M

/-- Every represented interior cell is a positive prime bounded by the
finite prime-table invariant. -/
theorem LimitTableRep.cell_prime_bounds {c : Cfg} {s : AState}
    {ps : List Nat} {guard bound k : Nat}
    (hRep : LimitTableRep c s ps guard)
    (hInv : PrimeTableInv ps bound)
    (hk : k < ps.length) :
    0 < s.arr (c.primeBase + k) ∧
      s.arr (c.primeBase + k) ≤ bound := by
  have hp : IsPrime (s.arr (c.primeBase + k)) :=
    TablePrefix.cell_property hRep.table hInv.sound k hk
  have hu : s.arr (c.primeBase + k) ≤ bound :=
    TablePrefix.cell_property hRep.table hInv.upper k hk
  exact ⟨by have := hp.two_le; omega, hu⟩

/-- Two states with the same exact selected representation agree on every
cell observable by `cursorStep`, including the terminal guard. -/
theorem LimitTableRep.same_cell {c : Cfg} {s t : AState}
    {ps : List Nat} {guard k : Nat}
    (hs : LimitTableRep c s ps guard)
    (ht : LimitTableRep c t ps guard)
    (hk : k ≤ ps.length) :
    s.arr (c.primeBase + k) = t.arr (c.primeBase + k) := by
  by_cases hlt : k < ps.length
  · exact TablePrefix.cell_eq hs.table ht.table k hlt
  · have heq : k = ps.length := by omega
    rw [heq, hs.guard_eq, ht.guard_eq]

/-- Branch-sensitive word safety for an ordinary event at an arbitrary
selected cursor limit. -/
structure LimitNonstartReady (c : Cfg) (s : AState)
    (limit bound w : Nat) : Prop where
  nonstart : s.regs rR ≠ 0
  window_eq : s.regs rW = w
  cursor_le : s.regs rPi ≤ limit
  prime_pos : 0 < s.regs rP
  prime_lt_modulus : s.regs rP < M
  offset_lt_modulus : s.regs rJ < M
  live_prime_sq_lt_modulus : s.regs rJ < c.segLen →
    s.regs rP * s.regs rP < M
  live_next_offset_lt_modulus : s.regs rJ < c.segLen →
    s.regs rJ + s.regs rP < M
  live_value_lt_modulus : s.regs rJ < c.segLen →
    w + s.regs rJ < M
  live_divides : s.regs rJ < c.segLen →
    s.regs rP ∣ w + s.regs rJ

/-- Transfer the mathematical cursor invariant to exactly the word-safety
facts used by one generic-limit machine event. -/
theorem LimitNonstartReady.of_cursor (c : Cfg) (s : AState)
    (limit bound w : Nat)
    (hcursor : CursorMainReady c.segLen w limit bound (machineCursor s))
    (hR : s.regs rR ≠ 0)
    (hW : s.regs rW = w)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M) :
    LimitNonstartReady c s limit bound w := by
  change CursorMainReady c.segLen w limit bound
    { pi := s.regs rPi, p := s.regs rP, j := s.regs rJ } at hcursor
  have active_of_live (hj : s.regs rJ < c.segLen) :
      s.regs rPi < limit := by
    have hne : s.regs rPi ≠ limit := by
      intro heq
      have hterm := hcursor.terminal_exhausted heq
      have hterm' : c.segLen ≤ s.regs rJ := by simpa using hterm
      omega
    exact Nat.lt_of_le_of_ne hcursor.cursor_le hne
  constructor
  · exact hR
  · exact hW
  · exact hcursor.cursor_le
  · exact hcursor.prime_pos
  · exact hcursor.prime_lt_modulus
  · exact hcursor.offset_lt_modulus
  · intro hj
    have hpLe := hcursor.active_prime_le_bound (active_of_live hj)
    have hpLe' : s.regs rP ≤ bound := by simpa using hpLe
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hpLe' hpLe') hboundSqM
  · intro hj
    have hpLe := hcursor.active_prime_le_bound (active_of_live hj)
    have hpLe' : s.regs rP ≤ bound := by simpa using hpLe
    omega
  · intro hj
    omega
  · intro hj
    exact hcursor.live_divides hj

/-- Forgetting the selected limit leaves exactly the branch-sensitive safety
record used by the full-table framing theorem. -/
theorem LimitNonstartReady.toMain {c : Cfg} {s : AState}
    {limit bound w : Nat}
    (hready : LimitNonstartReady c s limit bound w)
    (hlimitLe : limit ≤ c.tableLen) :
    MainNonstartReady c s := by
  constructor
  · exact hready.nonstart
  · exact Nat.le_trans hready.cursor_le hlimitLe
  · exact hready.prime_pos
  · exact hready.prime_lt_modulus
  · exact hready.offset_lt_modulus
  · exact hready.live_prime_sq_lt_modulus
  · exact hready.live_next_offset_lt_modulus
  · intro hj
    rw [hready.window_eq]
    exact hready.live_value_lt_modulus hj
  · intro hj
    rw [hready.window_eq]
    exact hready.live_divides hj

/-- One ordinary marking event preserves the exact selected prefix and its
terminal guard. -/
theorem arun_coreBody_mark_preserves_limitTableRep_nonstart (c : Cfg)
    (idx : Nat) (s : AState) (ps : List Nat) (guard limit bound w : Nat)
    (hRep : LimitTableRep c s ps guard)
    (hpsLen : ps.length = limit)
    (hready : LimitNonstartReady c s limit bound w)
    (hmark : s.regs rR < c.markSteps)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hA : c.arrayLen < M) :
    LimitTableRep c (arun idx s c.coreBody) ps guard := by
  have hpiM : s.regs rPi < M :=
    Nat.lt_of_le_of_lt hready.cursor_le hlimitM
  constructor
  · apply TablePrefix.frame_cells hRep.table
    intro k hk
    exact arun_coreBody_mark_tableCell_nonstart c idx s k hmark
      hready.nonstart hTM hp1Pos hp1M hpiM hready.prime_pos
      hready.prime_lt_modulus hready.offset_lt_modulus
      hready.live_prime_sq_lt_modulus
      (fun hj => by rw [hready.window_eq]; exact
        hready.live_value_lt_modulus hj) hA
      (by rw [hpsLen] at hk; omega)
  · rw [hpsLen]
    exact (arun_coreBody_mark_tableCell_nonstart c idx s limit hmark
      hready.nonstart hTM hp1Pos hp1M hpiM hready.prime_pos
      hready.prime_lt_modulus hready.offset_lt_modulus
      hready.live_prime_sq_lt_modulus
      (fun hj => by rw [hready.window_eq]; exact
        hready.live_value_lt_modulus hj) hA hlimitLe).trans
      (by simpa [hpsLen] using hRep.guard_eq)
  · exact hRep.guard_pos
  · exact hRep.guard_lt_modulus

/-- The reset event also frames an arbitrary selected prefix and its guard. -/
theorem arun_coreBody_mark_preserves_limitTableRep_start (c : Cfg)
    (idx : Nat) (s : AState) (ps : List Nat) (guard limit : Nat)
    (hRep : LimitTableRep c s ps guard)
    (hpsLen : ps.length = limit)
    (hR : s.regs rR = 0)
    (hTPos : 0 < c.markSteps)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1M : c.firstPrime < M)
    (hp1SqM : c.firstPrime * c.firstPrime < M)
    (hnStartM :
      s.regs rW + firstOffset (s.regs rW) c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hlimitLe : limit ≤ c.tableLen) :
    LimitTableRep c (arun idx s c.coreBody) ps guard := by
  constructor
  · apply TablePrefix.frame_cells hRep.table
    intro k hk
    exact arun_coreBody_mark_tableCell_start c idx s k hR hTPos hTM
      hp1Pos hp1LeL hp1M hp1SqM hnStartM hA
      (by rw [hpsLen] at hk; omega)
  · rw [hpsLen]
    exact (arun_coreBody_mark_tableCell_start c idx s limit hR hTPos hTM
      hp1Pos hp1LeL hp1M hp1SqM hnStartM hA hlimitLe).trans
      (by simpa [hpsLen] using hRep.guard_eq)
  · exact hRep.guard_pos
  · exact hRep.guard_lt_modulus

/-- Terminal slack at an arbitrary selected limit realizes the clamped
schedule step and loads the represented positive guard. -/
theorem arun_coreBody_simulates_terminal_limit (c : Cfg) (idx : Nat)
    (s : AState) (ps : List Nat) (guard w limit : Nat)
    (hRep : LimitTableRep c s ps guard)
    (hpsLen : ps.length = limit)
    (hmark : s.regs rR < c.markSteps)
    (hR : s.regs rR ≠ 0)
    (hpi : s.regs rPi = limit)
    (hj : c.segLen ≤ s.regs rJ)
    (hw : s.regs rW = w)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hcurPM : s.regs rP < M)
    (hjM : s.regs rJ < M)
    (hA : c.arrayLen < M)
    (i : Nat) (hi : i < c.segLen) :
    machineScheduleState c i (arun idx s c.coreBody) =
      scheduleStep c.segLen w limit i
        (fun k => s.arr (c.primeBase + k))
        (machineScheduleState c i s) := by
  have htable : s.arr (c.primeBase + limit) = guard := by
    simpa [hpsLen] using hRep.guard_eq
  have hcur := arun_coreBody_cursor_terminal_nonstart_of_limit c idx s
    guard w limit hmark hR hpi hj hw hselectorLimit hlimitLe hTM
    hp1Pos hp1M hcurPM hjM htable hRep.guard_pos
    hRep.guard_lt_modulus hA
  have hcell := arun_coreBody_mark_exhausted_machineCell c idx s hmark hR
    hj hTM hp1Pos hp1M (by rw [hpi]; exact hlimitM) hcurPM hjM hA i hi
  have hmin : min (limit + 1) limit = limit :=
    Nat.min_eq_right (by omega)
  apply ScheduleState.ext
  · dsimp [machineScheduleState, machineCursor, scheduleStep, cursorStep]
    rw [hpi, if_neg (Nat.not_lt.mpr hj), hmin, htable]
    simp only [if_pos]
    rw [Cursor.mk.injEq]
    exact ⟨hcur.1, hcur.2.1, hcur.2.2.1⟩
  · dsimp [machineScheduleState, scheduleStep]
    simpa [machineCursor, Nat.not_lt.mpr hj] using hcell

/-- The live, advance, and terminal cursor cases form one machine simulation
theorem for an arbitrary represented finite limit. -/
theorem arun_coreBody_simulates_limit_nonstart (c : Cfg) (idx : Nat)
    (s : AState) (ps : List Nat) (guard bound w limit : Nat)
    (hRep : LimitTableRep c s ps guard)
    (hInv : PrimeTableInv ps bound)
    (hpsLen : ps.length = limit)
    (hready : LimitNonstartReady c s limit bound w)
    (hmark : s.regs rR < c.markSteps)
    (hselectorLimit :
      (arun idx s (selectorBlock c)).regs rLimit = limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hboundM : bound < M)
    (hA : c.arrayLen < M)
    (i : Nat) (hi : i < c.segLen) :
    machineScheduleState c i (arun idx s c.coreBody) =
      scheduleStep c.segLen w limit i
        (fun k => s.arr (c.primeBase + k))
        (machineScheduleState c i s) := by
  by_cases hj : s.regs rJ < c.segLen
  · have h := arun_coreBody_simulates_live_nonstart c idx s
      (s.regs rPi) (s.regs rP) (s.regs rJ) w limit hmark
      hready.nonstart rfl rfl rfl hready.window_eq hselectorLimit hj
      hready.cursor_le hlimitLe hlimitM hTM hp1Pos hp1M
      hready.prime_pos hready.prime_lt_modulus
      (hready.live_prime_sq_lt_modulus hj)
      (hready.live_next_offset_lt_modulus hj)
      (hready.live_value_lt_modulus hj) hA
      (hready.live_divides hj) i hi
    exact ScheduleState.ext h.1 h.2
  · have hjL : c.segLen ≤ s.regs rJ := Nat.le_of_not_gt hj
    by_cases hpiLt : s.regs rPi < limit
    · have hnextLe : s.regs rPi + 1 ≤ limit := by omega
      have hnextPos : 0 < s.arr (c.primeBase + (s.regs rPi + 1)) := by
        by_cases hnextLt : s.regs rPi + 1 < limit
        · exact (hRep.cell_prime_bounds hInv
            (by rwa [hpsLen])).1
        · have heq : s.regs rPi + 1 = limit := by omega
          rw [heq]
          exact htable_guard_pos
      have hnextM : s.arr (c.primeBase + (s.regs rPi + 1)) < M := by
        by_cases hnextLt : s.regs rPi + 1 < limit
        · have hb := hRep.cell_prime_bounds hInv (by rwa [hpsLen])
          omega
        · have heq : s.regs rPi + 1 = limit := by omega
          rw [heq]
          exact htable_guard_lt
      have h := arun_coreBody_simulates_advance_nonstart c idx s
        (s.regs rPi) (s.regs rP)
        (s.arr (c.primeBase + (s.regs rPi + 1))) (s.regs rJ) w limit
        hmark hready.nonstart rfl rfl rfl hready.window_eq
        hselectorLimit hjL hpiLt hlimitLe hlimitM hTM hp1Pos hp1M
        hready.prime_lt_modulus hready.offset_lt_modulus rfl hnextPos
        hnextM hA i hi
      exact ScheduleState.ext h.1 h.2
    · have hpiEq : s.regs rPi = limit :=
        Nat.le_antisymm hready.cursor_le (Nat.le_of_not_gt hpiLt)
      exact arun_coreBody_simulates_terminal_limit c idx s ps guard w
        limit hRep hpsLen hmark hready.nonstart hpiEq hjL
        hready.window_eq hselectorLimit hlimitLe hlimitM hTM hp1Pos
        hp1M hready.prime_lt_modulus hready.offset_lt_modulus hA i hi
where
  htable_guard_pos : 0 < s.arr (c.primeBase + limit) := by
    rw [show s.arr (c.primeBase + limit) = guard by
      simpa [hpsLen] using hRep.guard_eq]
    exact hRep.guard_pos
  htable_guard_lt : s.arr (c.primeBase + limit) < M := by
    rw [show s.arr (c.primeBase + limit) = guard by
      simpa [hpsLen] using hRep.guard_eq]
    exact hRep.guard_lt_modulus

/-- Strong finite simulation at an arbitrary selected limit.  Cursor safety,
table preservation, and machine/schedule equality are established together,
so no per-prefix arithmetic oracle is assumed. -/
theorem bodyRun_simulates_limit_nonstart_of_cursor (c : Cfg)
    (idx fuel : Nat) (s : AState) (ps : List Nat)
    (guard bound w limit i : Nat)
    (hRep : LimitTableRep c s ps guard)
    (hInv : PrimeTableInv ps bound)
    (hpsLen : ps.length = limit)
    (hcursor0 : CursorMainReady c.segLen w limit bound
      (machineScheduleState c i s).cursor)
    (hR : ∀ k, k < fuel → (bodyRun idx c k s).regs rR ≠ 0)
    (hmark : ∀ k, k < fuel →
      (bodyRun idx c k s).regs rR < c.markSteps)
    (hW : ∀ k, k < fuel → (bodyRun idx c k s).regs rW = w)
    (hselectorLimit : ∀ k, k < fuel →
      (arun idx (bodyRun idx c k s) (selectorBlock c)).regs rLimit =
        limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTM : c.markSteps < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1M : c.firstPrime < M)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hsegSuccM : c.segLen + 1 < M)
    (hwSegM : w + c.segLen < M)
    (hA : c.arrayLen < M)
    (hi : i < c.segLen) :
    machineScheduleState c i (bodyRun idx c fuel s) =
      scheduleRun fuel c.segLen w limit i
        (fun k => s.arr (c.primeBase + k))
        (machineScheduleState c i s) := by
  let table := fun q => s.arr (c.primeBase + q)
  have htablePrime : ∀ q, q < limit →
      0 < table q ∧ table q ≤ bound := by
    intro q hq
    exact hRep.cell_prime_bounds hInv (by rwa [hpsLen])
  have hguard : 0 < table limit ∧ table limit < M := by
    have heq : table limit = guard := by
      dsimp only [table]
      simpa [hpsLen] using hRep.guard_eq
    rw [heq]
    exact ⟨hRep.guard_pos, hRep.guard_lt_modulus⟩
  have go : ∀ n, n ≤ fuel →
      machineScheduleState c i (bodyRun idx c n s) =
          scheduleRun n c.segLen w limit i table
            (machineScheduleState c i s) ∧
        LimitTableRep c (bodyRun idx c n s) ps guard := by
    intro n hn
    induction n with
    | zero => exact ⟨rfl, hRep⟩
    | succ k ih =>
        have hk : k < fuel := by omega
        have hprev := ih (by omega)
        have hmodelReady := scheduleRun_cursor_main_ready k c.segLen w
          limit bound i table (machineScheduleState c i s) hcursor0
          htablePrime hguard hboundM hsegBoundM hsegSuccM
        have hmachineCursor : CursorMainReady c.segLen w limit bound
            (machineCursor (bodyRun idx c k s)) := by
          change CursorMainReady c.segLen w limit bound
            (machineScheduleState c i (bodyRun idx c k s)).cursor
          rw [hprev.1]
          exact hmodelReady
        have hreadyK := LimitNonstartReady.of_cursor c
          (bodyRun idx c k s) limit bound w hmachineCursor (hR k hk)
          (hW k hk) hboundSqM hsegBoundM hwSegM
        have hone := arun_coreBody_simulates_limit_nonstart c idx
          (bodyRun idx c k s) ps guard bound w limit hprev.2 hInv hpsLen
          hreadyK (hmark k hk) (hselectorLimit k hk) hlimitLe hlimitM
          hTM hp1Pos hp1M hboundM hA i hi
        have htableK : ∀ q, q ≤ limit →
            (bodyRun idx c k s).arr (c.primeBase + q) = table q := by
          intro q hq
          exact hprev.2.same_cell hRep (by rwa [hpsLen])
        have hsimNext :
            machineScheduleState c i
                (arun idx (bodyRun idx c k s) c.coreBody) =
              scheduleStep c.segLen w limit i table
                (scheduleRun k c.segLen w limit i table
                  (machineScheduleState c i s)) := by
          calc
            machineScheduleState c i
                (arun idx (bodyRun idx c k s) c.coreBody) =
                scheduleStep c.segLen w limit i
                  (fun q => (bodyRun idx c k s).arr
                    (c.primeBase + q))
                  (machineScheduleState c i (bodyRun idx c k s)) := hone
            _ = scheduleStep c.segLen w limit i table
                  (machineScheduleState c i (bodyRun idx c k s)) :=
              scheduleStep_table_congr c.segLen w limit i _ _ _ htableK
            _ = scheduleStep c.segLen w limit i table
                  (scheduleRun k c.segLen w limit i table
                    (machineScheduleState c i s)) := by rw [hprev.1]
        have hRepNext :=
          arun_coreBody_mark_preserves_limitTableRep_nonstart c idx
            (bodyRun idx c k s) ps guard limit bound w hprev.2 hpsLen
            hreadyK (hmark k hk) hlimitLe hlimitM hTM hp1Pos hp1M hA
        constructor
        · rw [bodyRun_succ, scheduleRun_succ]
          exact hsimNext
        · rw [bodyRun_succ]
          exact hRepNext
  exact (go fuel (Nat.le_refl _)).1

/-- Complete reset-plus-ordinary finite simulation at an arbitrary selected
limit.  The counter and window hypotheses are discharged from the verified
production position theorem. -/
theorem bodyRun_simulates_limit_from_start (c : Cfg)
    (idx fuel : Nat) (s : AState) (ps : List Nat)
    (guard bound w limit i : Nat)
    (hRep : LimitTableRep c s ps guard)
    (hInv : PrimeTableInv ps bound)
    (hpsLen : ps.length = limit)
    (hR : s.regs rR = 0)
    (hW : s.regs rW = w)
    (hfuel : fuel + 1 ≤ c.markSteps)
    (hselectorLimit : ∀ t : AState,
      (arun idx t (selectorBlock c)).regs rLimit = limit)
    (hlimitPos : 0 < limit)
    (hlimitLe : limit ≤ c.tableLen)
    (hlimitM : limit < M)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hidxNe : idx ≠ c.rootSpan - 1)
    (hwriteM : s.regs rWrite < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hi : i < c.segLen) :
    let first := arun idx s c.coreBody
    machineScheduleState c i (bodyRun idx c (fuel + 1) s) =
      scheduleRun fuel c.segLen w limit i
        (fun k => first.arr (c.primeBase + k))
        (scheduleStart c.segLen w c.firstPrime i (machineCell c s i)) := by
  let first := arun idx s c.coreBody
  have hTPos : 0 < c.markSteps := by omega
  have hLPos : 0 < c.segLen := by omega
  have hp1M : c.firstPrime < M := Nat.lt_of_le_of_lt hp1LeBound hboundM
  have hp1SqM : c.firstPrime * c.firstPrime < M :=
    Nat.lt_of_le_of_lt
      (Nat.mul_le_mul hp1LeBound hp1LeBound) hboundSqM
  have hsegSuccM : c.segLen + 1 < M := by omega
  have hwM : w < M := by omega
  have hstartPair := arun_coreBody_simulates_start c idx s w limit hR hW
    (hselectorLimit s) hlimitLe hlimitM hTPos hTM hp1Pos hp1LeL hp1M
    hp1SqM hnStartM hA i hi
  have hstartEq : machineScheduleState c i first =
      scheduleStart c.segLen w c.firstPrime i (machineCell c s i) := by
    exact ScheduleState.ext hstartPair.1 hstartPair.2
  have hRepFirst :=
    arun_coreBody_mark_preserves_limitTableRep_start c idx s ps guard limit
      hRep hpsLen hR hTPos hTM hp1Pos hp1LeL hp1M hp1SqM
      (by rw [hW]; exact hnStartM) hA hlimitLe
  have hcursorFirst : CursorMainReady c.segLen w limit bound
      (machineScheduleState c i first).cursor := by
    rw [hstartEq]
    exact scheduleStart_cursor_ready c.segLen w limit bound c.firstPrime i
      (machineCell c s i) hlimitPos hp1Pos hp1LeL hp1LeBound hboundM
      hsegBoundM
  have hposition (n : Nat) (hn : n ≤ fuel + 1) :
      (bodyRun idx c n s).regs rWrite = s.regs rWrite ∧
        (bodyRun idx c n s).regs rR = n ∧
        (bodyRun idx c n s).regs rW = w :=
    bodyRun_mark_position c idx n s w (s.regs rWrite) (by omega) hR hW
      rfl hLPos hTM hPM hidxM hspanM hidxNe hwriteM hwM
  have hpositionFirst (k : Nat) (hk : k ≤ fuel) :
      (bodyRun idx c k first).regs rWrite = s.regs rWrite ∧
        (bodyRun idx c k first).regs rR = k + 1 ∧
        (bodyRun idx c k first).regs rW = w := by
    have hp := hposition (k + 1) (by omega)
    rw [bodyRun_succ_start] at hp
    simpa [first, Nat.add_comm] using hp
  have hsim := bodyRun_simulates_limit_nonstart_of_cursor c idx fuel first
    ps guard bound w limit i hRepFirst hInv hpsLen hcursorFirst
    (fun k hk => by rw [(hpositionFirst k (by omega)).2.1]; omega)
    (fun k hk => by rw [(hpositionFirst k (by omega)).2.1]; omega)
    (fun k hk => (hpositionFirst k (by omega)).2.2)
    (fun k _ => hselectorLimit (bodyRun idx c k first)) hlimitLe
    hlimitM hTM hp1Pos hp1M hboundM hboundSqM hsegBoundM hsegSuccM
    hwSegM hA hi
  rw [bodyRun_succ_start]
  exact hsim.trans (by rw [hstartEq])

/-- Root-phase specialization: the production selector chooses exactly the
bootstrap count at every state of a nonfinal root index. -/
theorem bodyRun_simulates_root_from_start (c : Cfg)
    (idx fuel : Nat) (s : AState) (boot : List Nat)
    (guard bound w i : Nat)
    (hRep : LimitTableRep c s boot guard)
    (hInv : PrimeTableInv boot bound)
    (hbootLen : boot.length = c.bootCount)
    (hR : s.regs rR = 0)
    (hW : s.regs rW = w)
    (hfuel : fuel + 1 ≤ c.markSteps)
    (hrootInterior : idx < c.rootSpan - 1)
    (hbootPos : 0 < c.bootCount)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hwriteM : s.regs rWrite < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hi : i < c.segLen) :
    let first := arun idx s c.coreBody
    machineScheduleState c i (bodyRun idx c (fuel + 1) s) =
      scheduleRun fuel c.segLen w c.bootCount i
        (fun k => first.arr (c.primeBase + k))
        (scheduleStart c.segLen w c.firstPrime i (machineCell c s i)) := by
  have hroot : idx < c.rootSpan := by omega
  have hidxNe : idx ≠ c.rootSpan - 1 := by omega
  apply bodyRun_simulates_limit_from_start c idx fuel s boot guard bound w
    c.bootCount i hRep hInv hbootLen hR hW hfuel
  · intro t
    exact (selectorBlock_limit_root c idx t hroot hidxM hspanM hbootLe
      htableLenM).1
  · exact hbootPos
  · exact hbootLe
  · omega
  · exact hTM
  · exact hPM
  · exact hidxM
  · exact hspanM
  · exact hidxNe
  · exact hwriteM
  · exact hp1Pos
  · exact hp1LeL
  · exact hp1LeBound
  · exact hboundM
  · exact hboundSqM
  · exact hsegBoundM
  · exact hwSegM
  · exact hnStartM
  · exact hA
  · exact hi

/-- A completed arbitrary-limit machine schedule computes the mathematical
finite prime-list fold for its selected cell. -/
theorem machineCell_eq_rootCellFoldFrom_of_limit_schedule
    (c : Cfg) (first out : AState) (cell : RootCellState)
    (ps : List Nat) (guard bound w limit i : Nat)
    (hRep : LimitTableRep c first (c.firstPrime :: ps) guard)
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hpsLen : (c.firstPrime :: ps).length = limit)
    (hpLe : c.firstPrime ≤ c.segLen)
    (hbudget :
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hi : i < c.segLen)
    (hsim : machineScheduleState c i out =
      scheduleRun (c.markSteps - 1) c.segLen w limit i
        (fun k => first.arr (c.primeBase + k))
        (scheduleStart c.segLen w c.firstPrime i cell)) :
    machineCell c out i =
      rootCellFoldFrom (w + i) cell (c.firstPrime :: ps) := by
  have htable : CursorTable
      (fun k => first.arr (c.primeBase + k)) 0
      (c.firstPrime :: ps) := by
    simpa using cursorTable_of_tablePrefix first.arr c.primeBase 0
      (c.firstPrime :: ps) (by simpa using hRep.table)
  have hpos : ∀ p, p ∈ c.firstPrime :: ps → 0 < p := by
    intro p hp
    have := (hInv.sound p hp).two_le
    omega
  have hfuel : cursorScheduleFuel c.segLen w (c.firstPrime :: ps) ≤
      c.markSteps :=
    Nat.le_trans
      (cursorScheduleFuel_le_primeBudget c.segLen w (c.firstPrime :: ps))
      hbudget
  have hpure := scheduleRun_from_start_cell_eq_rootCellFoldFrom_of_budget
    c.markSteps c.segLen w limit c.firstPrime i
    (fun k => first.arr (c.primeBase + k)) cell ps htable hpsLen hpos
    hpLe hfuel hi
  have hcell := congrArg ScheduleState.cell hsim
  change machineCell c out i = _ at hcell
  exact hcell.trans hpure

/-- Complete compiled marking theorem for one nonfinal root window.  Unlike
the main-table theorem, its cursor consumes exactly the bootstrap prefix
selected by the production root branch. -/
theorem bodyRun_root_cell_eq_rootCellFoldFrom
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (guard bound w i : Nat)
    (hRep : LimitTableRep c s (c.firstPrime :: ps) guard)
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hbootLen : (c.firstPrime :: ps).length = c.bootCount)
    (hR : s.regs rR = 0)
    (hW : s.regs rW = w)
    (hrootInterior : idx < c.rootSpan - 1)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M)
    (hPM : c.period < M)
    (hidxM : idx < M)
    (hspanM : c.rootSpan < M)
    (hwriteM : s.regs rWrite < M)
    (hp1Pos : 0 < c.firstPrime)
    (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound)
    (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hi : i < c.segLen) :
    machineCell c (bodyRun idx c c.markSteps s) i =
      rootCellFoldFrom (w + i) (machineCell c s i)
        (c.firstPrime :: ps) := by
  let first := arun idx s c.coreBody
  have hsumPos : 0 <
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum := by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_pos_left (Nat.add_pos_right _ (by decide : 0 < 2)) _
  have hTPos : 0 < c.markSteps := Nat.lt_of_lt_of_le hsumPos hbudget
  have hbootPos : 0 < c.bootCount := by
    rw [← hbootLen]
    simp
  have hp1M : c.firstPrime < M := Nat.lt_of_le_of_lt hp1LeBound hboundM
  have hp1SqM : c.firstPrime * c.firstPrime < M :=
    Nat.lt_of_le_of_lt
      (Nat.mul_le_mul hp1LeBound hp1LeBound) hboundSqM
  have hRepFirst : LimitTableRep c first (c.firstPrime :: ps) guard := by
    dsimp only [first]
    exact arun_coreBody_mark_preserves_limitTableRep_start c idx s
      (c.firstPrime :: ps) guard c.bootCount hRep hbootLen hR hTPos hTM
      hp1Pos hp1LeL hp1M hp1SqM (by rw [hW]; exact hnStartM) hA
      hbootLe
  have hsim := bodyRun_simulates_root_from_start c idx
    (c.markSteps - 1) s (c.firstPrime :: ps) guard bound w i hRep hInv
    hbootLen hR hW (by omega) hrootInterior hbootPos hbootLe htableLenM
    hTM hPM hidxM hspanM hwriteM hp1Pos hp1LeL hp1LeBound hboundM
    hboundSqM hsegBoundM hwSegM hnStartM hA hi
  have hsteps : c.markSteps - 1 + 1 = c.markSteps := by omega
  rw [hsteps] at hsim
  exact machineCell_eq_rootCellFoldFrom_of_limit_schedule c first
    (bodyRun idx c c.markSteps s) (machineCell c s i) ps guard bound w
    c.bootCount i hRepFirst hInv hbootLen hp1LeL hbudget hi hsim

/-- Cleared-cell root specialization used by the outer root-window
induction. -/
theorem bodyRun_root_cell_eq_rootCellFold
    (c : Cfg) (idx : Nat) (s : AState) (ps : List Nat)
    (guard bound w i : Nat)
    (hRep : LimitTableRep c s (c.firstPrime :: ps) guard)
    (hInv : PrimeTableInv (c.firstPrime :: ps) bound)
    (hbootLen : (c.firstPrime :: ps).length = c.bootCount)
    (hR : s.regs rR = 0) (hW : s.regs rW = w)
    (hrootInterior : idx < c.rootSpan - 1)
    (hbootLe : c.bootCount ≤ c.tableLen)
    (htableLenM : c.tableLen < M)
    (hTM : c.markSteps < M) (hPM : c.period < M)
    (hidxM : idx < M) (hspanM : c.rootSpan < M)
    (hwriteM : s.regs rWrite < M)
    (hp1Pos : 0 < c.firstPrime) (hp1LeL : c.firstPrime ≤ c.segLen)
    (hp1LeBound : c.firstPrime ≤ bound) (hboundM : bound < M)
    (hboundSqM : bound * bound < M)
    (hsegBoundM : c.segLen + bound < M)
    (hwSegM : w + c.segLen < M)
    (hnStartM : w + firstOffset w c.firstPrime < M)
    (hA : c.arrayLen < M)
    (hbudget :
      ((c.firstPrime :: ps).map fun p => c.segLen / p + 2).sum ≤
        c.markSteps)
    (hi : i < c.segLen)
    (hclear : machineCell c s i = ⟨0, 0⟩) :
    machineCell c (bodyRun idx c c.markSteps s) i =
      rootCellFold (c.firstPrime :: ps) (w + i) := by
  rw [bodyRun_root_cell_eq_rootCellFoldFrom c idx s ps guard bound w i
    hRep hInv hbootLen hR hW hrootInterior hbootLe htableLenM hTM hPM
    hidxM hspanM hwriteM hp1Pos hp1LeL hp1LeBound hboundM hboundSqM
    hsegBoundM hwSegM hnStartM hA hbudget hi, hclear]
  rfl

end LeanCompCert.Ports.ArraySegMobiusRootMarkFold

import LeanCompCert.Ports.ArraySegMobiusScheduleFold
import LeanCompCert.Ports.RamareCombined100MMarkInvariant

/-!
# Cursor enumeration for the Ramaré seven-plane marking loop

This module connects the production residue cursor to the logical
prime-power fold.  It reuses the finite arithmetic-progression proof from the
segmented Möbius sieve and changes only the selected-cell action: a live event
applies `PlaneCell.markPower` to the seven Ramaré planes.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.ArraySegMobiusMark
open LeanCompCert.Ports.ArraySegMobiusScheduleFold
open LeanCompCert.Ports.RamareCombined100MSeg

/-- Apply a finite list of physical `(offset, power)` events to one selected
seven-plane cell.  Events for every other offset are frames. -/
def planeEventCellFold (i base : Nat) (events : List (Nat × Nat))
    (x : PlaneCell) : PlaneCell :=
  events.foldl
    (fun q event => if event.1 = i then q.markPower event.2 base else q) x

/-- A positive arithmetic progression reaches a selected offset at most once,
so its complete physical effect is either one `markPower` or a frame. -/
theorem planeEventCellFold_progression (count i j pow base : Nat)
    (x : PlaneCell) (hpow : 0 < pow) :
    planeEventCellFold i base
        ((List.range count).map (fun t => (j + t * pow, pow))) x =
      if ∃ t, t < count ∧ j + t * pow = i then
        x.markPower pow base
      else x := by
  induction count generalizing x with
  | zero => simp [planeEventCellFold]
  | succ count ih =>
      rw [List.range_succ, List.map_append]
      simp only [planeEventCellFold, List.foldl_append, List.map_cons,
        List.map_nil, List.foldl_cons, List.foldl_nil]
      change (if j + count * pow = i then
          (planeEventCellFold i base
            ((List.range count).map (fun t => (j + t * pow, pow))) x).markPower
              pow base
        else
          planeEventCellFold i base
            ((List.range count).map (fun t => (j + t * pow, pow))) x) = _
      by_cases hlast : j + count * pow = i
      · have hnone : ¬∃ t, t < count ∧ j + t * pow = i := by
          intro h
          rcases h with ⟨t, ht, heq⟩
          have hmul : t * pow = count * pow := by omega
          have : t = count := Nat.mul_right_cancel hpow hmul
          omega
        have hsucc : ∃ t, t < count + 1 ∧ j + t * pow = i :=
          ⟨count, by omega, hlast⟩
        rw [if_pos hlast, ih, if_neg hnone, if_pos hsucc]
      · by_cases hprev : ∃ t, t < count ∧ j + t * pow = i
        · have hsucc : ∃ t, t < count + 1 ∧ j + t * pow = i := by
            rcases hprev with ⟨t, ht, heq⟩
            exact ⟨t, by omega, heq⟩
          rw [if_neg hlast, ih, if_pos hprev, if_pos hsucc]
        · have hnoneSucc : ¬∃ t, t < count + 1 ∧ j + t * pow = i := by
            intro h
            rcases h with ⟨t, ht, heq⟩
            by_cases htCount : t < count
            · exact hprev ⟨t, htCount, heq⟩
            · have htEq : t = count := by omega
              subst t
              exact hlast heq
          rw [if_neg hlast, ih, if_neg hprev, if_neg hnoneSucc]

/-- The Ramaré production offset formula is definitionally the already-audited
segmented-sieve `firstOffset`. -/
theorem startOffset_eq_firstOffset (w pow : Nat) :
    startOffset w pow = firstOffset w pow := rfl

/-- Exact live cursor block for one prime power, phrased with the Ramaré
production `startOffset`. -/
def powerCursorEvents (segLen w pow : Nat) : List (Nat × Nat) :=
  cursorLiveEvents segLen (startOffset w pow) pow

/-- One finite positive-power cursor block marks the selected cell exactly
when the represented integer is divisible by that power. -/
theorem planeEventCellFold_powerCursorEvents (segLen w i pow base : Nat)
    (x : PlaneCell) (hpow : 0 < pow) (hi : i < segLen) :
    planeEventCellFold i base (powerCursorEvents segLen w pow) x =
      if pow ∣ w + i then x.markPower pow base else x := by
  rw [powerCursorEvents, startOffset_eq_firstOffset,
    cursorLiveEvents, planeEventCellFold_progression _ i
      (firstOffset w pow) pow base x hpow]
  by_cases hdiv : pow ∣ w + i
  · rw [if_pos hdiv,
      if_pos ((mem_cursor_progression_iff segLen w i pow hpow hi).2 hdiv)]
  · have hnone : ¬∃ t, t < liveCount segLen (firstOffset w pow) pow ∧
        firstOffset w pow + t * pow = i := by
      intro h
      exact hdiv ((mem_cursor_progression_iff segLen w i pow hpow hi).1 h)
    rw [if_neg hdiv, if_neg hnone]

/-- Runnable selected-cell view of one production power cursor. -/
def cursorPowerFold (segLen w i pow base : Nat) (x : PlaneCell) : PlaneCell :=
  planeEventCellFold i base (powerCursorEvents segLen w pow) x

theorem cursorPowerFold_eq (segLen w i pow base : Nat) (x : PlaneCell)
    (hpow : 0 < pow) (hi : i < segLen) :
    cursorPowerFold segLen w i pow base x =
      if pow ∣ w + i then x.markPower pow base else x := by
  exact planeEventCellFold_powerCursorEvents segLen w i pow base x hpow hi

/-! ## The complete 32-power block for one prime -/

/-- Divisible exponents in one finite consecutive exponent interval. -/
def powerHitExponents (p n start count : Nat) : List Nat :=
  (List.range' start count).filter (fun j => decide (p ^ j ∣ n))

/-- If one power misses, every higher power misses as well. -/
theorem pow_not_dvd_of_not_dvd_of_le (p n a b : Nat) (hab : a ≤ b)
    (ha : ¬p ^ a ∣ n) : ¬p ^ b ∣ n := by
  intro hb
  exact ha (Nat.dvd_trans (Nat.pow_dvd_pow p hab) hb)

/-- Prime-power divisibility is a prefix condition.  Consequently the list of
physical power hits is exactly the consecutive exponent range whose length is
the source-model exponent count. -/
theorem powerHitExponents_eq_range' (p n start count : Nat) :
    powerHitExponents p n start count =
      List.range' start (powerHitExponents p n start count).length := by
  induction count generalizing start with
  | zero => simp [powerHitExponents]
  | succ count ih =>
      change
        List.filter (fun j => decide (p ^ j ∣ n))
            (List.range' start (count + 1)) =
          List.range' start
            (List.filter (fun j => decide (p ^ j ∣ n))
              (List.range' start (count + 1))).length
      rw [List.range'_succ]
      by_cases hhit : p ^ start ∣ n
      · simp only [List.filter_cons, decide_eq_true_eq, hhit, if_true,
          List.length_cons, List.range'_succ]
        congr 1
        simpa [powerHitExponents] using ih (start + 1)
      · have htail : powerHitExponents p n (start + 1) count = [] := by
          rw [powerHitExponents, List.filter_eq_nil_iff]
          intro j hj
          rw [decide_eq_true_eq]
          apply pow_not_dvd_of_not_dvd_of_le p n start j (by
            rw [List.mem_range'] at hj
            rcases hj with ⟨t, _, rfl⟩
            omega) hhit
        have htailRaw :
            List.filter (fun j => decide (p ^ j ∣ n))
              (List.range' (start + 1) count) = [] := by
          simpa [powerHitExponents] using htail
        simp only [List.filter_cons, decide_eq_true_eq, hhit, if_false]
        rw [htailRaw]
        rfl

/-- Counting hits with the source `foldl` is the length of the corresponding
finite filtered exponent list. -/
theorem foldl_power_hit_count (p n : Nat) (js : List Nat) (acc : Nat) :
    js.foldl (fun count j => if p ^ j ∣ n then count + 1 else count) acc =
      acc + (js.filter (fun j => decide (p ^ j ∣ n))).length := by
  induction js generalizing acc with
  | nil => simp
  | cons j js ih =>
      by_cases hhit : p ^ j ∣ n
      · simp [hhit, ih, Nat.add_assoc, Nat.add_comm]
      · simp [hhit, ih]

theorem exponent32_eq_powerHitExponents_length (p n : Nat) :
    exponent32 p n = (powerHitExponents p n 1 32).length := by
  simpa [exponent32, powerHitExponents] using
    foldl_power_hit_count p n (List.range' 1 32) 0

/-- Execute the production cursor block for each power exponent in `js`. -/
def cursorPowerListFold (segLen w i p : Nat) (js : List Nat)
    (x : PlaneCell) : PlaneCell :=
  js.foldl
    (fun q j => cursorPowerFold segLen w i (p ^ j) p q) x

/-- Extensional selected-cell semantics of an arbitrary finite list of
positive-base power cursors. -/
theorem cursorPowerListFold_eq_hits (segLen w i p : Nat) (js : List Nat)
    (x : PlaneCell) (hp : 0 < p) (hi : i < segLen) :
    cursorPowerListFold segLen w i p js x =
      (js.filter (fun j => decide (p ^ j ∣ w + i))).foldl
        (fun q j => q.markPower (p ^ j) p) x := by
  induction js generalizing x with
  | nil => rfl
  | cons j js ih =>
      simp only [cursorPowerListFold, List.foldl_cons]
      rw [cursorPowerFold_eq segLen w i (p ^ j) p x (Nat.pow_pos hp) hi]
      by_cases hhit : p ^ j ∣ w + i
      · simp only [hhit, if_true, List.filter_cons, decide_eq_true_eq,
          List.foldl_cons]
        exact ih (x.markPower (p ^ j) p)
      · simp only [hhit, if_false, List.filter_cons, decide_eq_true_eq]
        exact ih x

/-- Runnable selected-cell view of all 32 production power cursors for one
table prime. -/
def cursorPrimePowerFold (segLen w i p : Nat) (x : PlaneCell) : PlaneCell :=
  cursorPowerListFold segLen w i p (List.range' 1 32) x

/-- The complete finite production cursor block for one prime is exactly the
logical `markRange` block used by `RamareCombined100MSeg.markPrime`. -/
theorem cursorPrimePowerFold_eq_markRange (segLen w i p : Nat)
    (x : PlaneCell) (hp : 0 < p) (hi : i < segLen) :
    cursorPrimePowerFold segLen w i p x =
      markRange x p 1 (exponent32 p (w + i)) := by
  rw [cursorPrimePowerFold,
    cursorPowerListFold_eq_hits segLen w i p (List.range' 1 32) x hp hi]
  change (powerHitExponents p (w + i) 1 32).foldl
      (fun q j => q.markPower (p ^ j) p) x = _
  rw [powerHitExponents_eq_range',
    exponent32_eq_powerHitExponents_length]
  rfl

/-! ## Table-row cursor fold -/

/-- Selected-cell view of the complete physical cursor schedule for a list of
table rows. -/
def cursorRowsFold (segLen w i : Nat) (rows : List PrimeRow)
    (x : PlaneCell) : PlaneCell :=
  rows.foldl
    (fun q row => cursorPrimePowerFold segLen w i row.p q) x

/-- Row-wise physical cursor enumeration is exactly the logical prime-row
power fold at the represented integer `w + i`. -/
theorem cursorRowsFold_eq_markRows (segLen w i : Nat) (rows : List PrimeRow)
    (x : PlaneCell) (hpos : ∀ row ∈ rows, 0 < row.p)
    (hi : i < segLen) :
    cursorRowsFold segLen w i rows x = markRows rows (w + i) x := by
  induction rows generalizing x with
  | nil => rfl
  | cons row rows ih =>
      simp only [cursorRowsFold, List.foldl_cons, markRows]
      rw [cursorPrimePowerFold_eq_markRange segLen w i row.p x
        (hpos row (by simp)) hi]
      exact ih (markRange x row.p 1 (exponent32 row.p (w + i)))
        (fun q hq => hpos q (by simp [hq]))

/-- For a positive, duplicate-free prime list, the complete physical cursor
schedule from seven zero planes refines the paper-facing `markCell`. -/
theorem cursorRows_factorRows_refines (segLen w i : Nat) (ps : List Nat)
    (hi : i < segLen) (htwo : ∀ p ∈ ps, 2 ≤ p) (hnodup : ps.Nodup) :
    CellRel
      (cursorRowsFold segLen w i (factorRows ps) emptyPlaneCell)
      (markCell (factorRows ps) (w + i)) := by
  rw [cursorRowsFold_eq_markRows segLen w i (factorRows ps) emptyPlaneCell
    (by
      intro row hrow
      simp only [factorRows, List.mem_map] at hrow
      obtain ⟨p, hp, rfl⟩ := hrow
      exact Nat.lt_of_lt_of_le Nat.zero_lt_two (htwo p hp)) hi]
  exact markRows_factorRows_refines ps (w + i) htwo hnodup

/-- Production `Cfg.ofChain` table specialization: its complete finite cursor
schedule has the exact source-model cell for every selected window offset. -/
theorem ofChain_cursorRows_refines (lo segLen segCount tableHi w i : Nat)
    (hi : i < segLen) :
    CellRel
      (cursorRowsFold segLen w i
        (factorRows (Cfg.ofChain lo segLen segCount tableHi).table)
        emptyPlaneCell)
      (markCell
        (factorRows (Cfg.ofChain lo segLen segCount tableHi).table)
        (w + i)) := by
  apply cursorRows_factorRows_refines
  · exact hi
  · intro p hp
    exact trialPrimesBelow_two_le _ p hp
  · exact trialPrimesBelow_nodup _

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

import LeanCompCert.Ports.Prop1224CellMarkSourceCell

/-!
# Source invariants and word guards for a Proposition 12.2.4 marking window

These lemmas turn the number-theoretic fact that the current radical remains
a divisor of its represented candidate into the fixed-width premises of the
literal marking theorem.  Iteration is symbolic in the fuel; no table or
window is evaluated by Lean.
-/

namespace LeanCompCert.Ports.Prop1224Cell

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState

/-- Every logical live cell satisfies the local radical/totient/bit
invariant. -/
def P1224MarkWindow.CellsInv (w : P1224MarkWindow) : Prop :=
  ∀ i, (w.cells i).Inv

/-- The current resident radical, including the next distinct base on a
first-power visit, still fits inside the represented candidate. -/
def P1224MarkWindow.ResidentRadicalReady
    (c : CellCfg) (windowBase : Nat) (w : P1224MarkWindow) : Prop :=
  w.cursor.offset < c.segLen →
    (w.cells w.cursor.offset).radical *
        (if w.cursor.first = 1 then w.cursor.base else 1) ≤
      windowBase + w.cursor.offset

/-- A logical marking step can only preserve a radical or multiply it by one
new base, so every pre-step radical divides the corresponding post-step
radical. -/
theorem P1224MarkWindow.cell_radical_dvd_step
    (c : CellCfg) (windowBase : Nat) (tableWord : Nat → Nat)
    (w : P1224MarkWindow) (i : Nat) :
    (w.cells i).radical ∣
      ((w.step c windowBase tableWord).cells i).radical := by
  by_cases hresident : w.cursor.offset < c.segLen
  · simp only [P1224MarkWindow.step, hresident, if_true]
    by_cases hi : i = w.cursor.offset
    · subst i
      simp only [updateP1224Cell, if_pos rfl]
      by_cases hfirst : w.cursor.first = 1
      · simp [P1224MarkCell.markPower, hfirst]
        exact ⟨w.cursor.base, rfl⟩
      · simp [P1224MarkCell.markPower, hfirst]
    · simp [updateP1224Cell, hi]
  · simp [P1224MarkWindow.step, hresident]

/-- Prefix radicals divide the matching radicals after any further symbolic
number of marking steps. -/
theorem P1224MarkWindow.cell_radical_dvd_run
    (fuel : Nat) (c : CellCfg) (windowBase : Nat)
    (tableWord : Nat → Nat) (w : P1224MarkWindow) (i : Nat) :
    (w.cells i).radical ∣
      ((w.run fuel c windowBase tableWord).cells i).radical := by
  induction fuel with
  | zero =>
      change (w.cells i).radical ∣ (w.cells i).radical
      exact ⟨1, by simp⟩
  | succ fuel ih =>
      change (w.cells i).radical ∣
        (((w.run fuel c windowBase tableWord).step c windowBase
          tableWord).cells i).radical
      rcases ih with ⟨a, ha⟩
      rcases P1224MarkWindow.cell_radical_dvd_step c windowBase tableWord
          (w.run fuel c windowBase tableWord) i with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      rw [hb, ha]
      simp [Nat.mul_assoc]

/-- At a resident cursor the exact radical required by the literal multiply
is precisely the post-step logical radical. -/
theorem P1224MarkWindow.resident_product_eq_step_radical
    (c : CellCfg) (windowBase : Nat) (tableWord : Nat → Nat)
    (w : P1224MarkWindow)
    (hresident : w.cursor.offset < c.segLen) :
    (w.cells w.cursor.offset).radical *
        (if w.cursor.first = 1 then w.cursor.base else 1) =
      ((w.step c windowBase tableWord).cells w.cursor.offset).radical := by
  simp only [P1224MarkWindow.step, hresident, if_true, updateP1224Cell,
    if_pos rfl]
  by_cases hfirst : w.cursor.first = 1
  · simp [P1224MarkCell.markPower, hfirst]
  · simp [P1224MarkCell.markPower, hfirst]

/-- Decode the zero/one source cursor word into the Boolean consumed by the
logical cell transition. -/
theorem P1224MarkCursor.first_eq_bool (cur : P1224MarkCursor)
    (hfirst : cur.first ≤ 1) :
    cur.first = if cur.first = 1 then 1 else 0 := by
  split
  · assumption
  · omega

/-- A pointwise invariant survives one source window step whenever a
resident cursor carries a genuine base `>= 2`.  Past-window rounds do not
touch logical live cells. -/
theorem P1224MarkWindow.CellsInv.step
    {c : CellCfg} {windowBase : Nat} {tableWord : Nat → Nat}
    {w : P1224MarkWindow} (hinv : w.CellsInv)
    (hbase : w.cursor.offset < c.segLen → 2 ≤ w.cursor.base) :
    (w.step c windowBase tableWord).CellsInv := by
  intro i
  by_cases hresident : w.cursor.offset < c.segLen
  · simp only [P1224MarkWindow.step, hresident, if_true]
    by_cases hi : i = w.cursor.offset
    · subst i
      simp only [updateP1224Cell, if_pos rfl]
      exact (hinv w.cursor.offset).markPower w.cursor.base
        (w.cursor.first = 1) (hbase hresident)
    · simp only [updateP1224Cell, if_neg hi]
      exact hinv i
  · simp only [P1224MarkWindow.step, hresident, if_false]
    exact hinv i

/-- Symbolic finite preservation.  The only schedule-specific premise is
that every actually resident pre-cursor has a base at least two; terminal
sentinel rows may still carry base one because they are never resident. -/
theorem P1224MarkWindow.CellsInv.run
    (fuel : Nat) {c : CellCfg} {windowBase : Nat}
    {tableWord : Nat → Nat} {w : P1224MarkWindow}
    (hinv : w.CellsInv)
    (hbase : ∀ t, t < fuel →
      let cur := w.cursor.run t c windowBase tableWord
      cur.offset < c.segLen → 2 ≤ cur.base) :
    (w.run fuel c windowBase tableWord).CellsInv := by
  induction fuel with
  | zero => exact hinv
  | succ fuel ih =>
      have hprefix : (w.run fuel c windowBase tableWord).CellsInv :=
        ih (fun t ht => hbase t (by omega))
      apply hprefix.step
      intro hresident
      have hcursor := P1224MarkWindow.run_cursor fuel c windowBase tableWord w
      rw [hcursor] at hresident ⊢
      exact hbase fuel (by omega) hresident

/-- Source radical readiness and a candidate ceiling discharge all cell-word
guards of one resident literal multiplication. -/
theorem P1224MarkWindow.resident_mark_words
    {c : CellCfg} {windowBase ceiling : Nat} {w : P1224MarkWindow}
    (hinv : w.CellsInv) (hready : w.ResidentRadicalReady c windowBase)
    (hresident : w.cursor.offset < c.segLen)
    (hcandidate : windowBase + w.cursor.offset ≤ ceiling)
    (hceiling : ceiling < M) :
    let first : Bool := w.cursor.first = 1
    (w.cells w.cursor.offset).radical *
          (if first then w.cursor.base else 1) < M ∧
    (w.cells w.cursor.offset).phiSmall *
          (if first then w.cursor.base - 1 else 1) < M ∧
      (w.cells w.cursor.offset).sqf ≤ 1 ∧
      (w.cells w.cursor.offset).sqf < M := by
  apply (hinv w.cursor.offset).mark_words
  by_cases hfirst : w.cursor.first = 1
  · simp only [hfirst, decide_true, Bool.true_eq, if_true]
    exact Nat.lt_of_le_of_lt (by simpa [hfirst] using hready hresident)
      (Nat.lt_of_le_of_lt hcandidate hceiling)
  · simp only [hfirst, decide_false, Bool.false_eq_true, if_false]
    exact Nat.lt_of_le_of_lt (by simpa [hfirst] using hready hresident)
      (Nat.lt_of_le_of_lt hcandidate hceiling)

/-- Physical plane loads agree with the same logical source cell. -/
theorem P1224MarkWindow.Rep.resident_plane_words
    {c : CellCfg} {s : AState} {w : P1224MarkWindow}
    (hrep : w.Rep c s) (hresident : w.cursor.offset < c.segLen) :
    p1224PlaneWordsAt s c.segLen w.cursor.offset =
      (w.cells w.cursor.offset).encode :=
  hrep.2 w.cursor.offset hresident

#print axioms P1224MarkCursor.first_eq_bool
#print axioms P1224MarkWindow.cell_radical_dvd_step
#print axioms P1224MarkWindow.cell_radical_dvd_run
#print axioms P1224MarkWindow.resident_product_eq_step_radical
#print axioms P1224MarkWindow.CellsInv.step
#print axioms P1224MarkWindow.CellsInv.run
#print axioms P1224MarkWindow.resident_mark_words
#print axioms P1224MarkWindow.Rep.resident_plane_words

end LeanCompCert.Ports.Prop1224Cell

import LeanCompCert.Ports.RamareCombined100MMarkRefinement

/-!
# Logical invariant for the Ramaré seven-plane marking loop

This file identifies the ordered prime-power events of the physical sieve with
the source-shaped `RamareCombined100MSeg.markPrime` update.  It remains
separate from the instruction proofs so algebraic induction cannot inflate the
compiler-facing module.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.RamareCombined100MSeg

def emptyPlaneCell : PlaneCell := ⟨0, 0, 0, 0, 0, 0, 0⟩

def onePrimeCell (prod p pe pProd : Nat) : PlaneCell :=
  ⟨prod, p, pe, pProd, 0, 0, 0⟩

def twoPrimeCell (prod p pe pProd q qe qProd : Nat) : PlaneCell :=
  ⟨prod, p, pe, pProd, q, qe, qProd⟩

/-- Fold the prime powers `p^start, ..., p^(start+count-1)` through one
physical cell. -/
def markRange (x : PlaneCell) (p start count : Nat) : PlaneCell :=
  (List.range' start count).foldl
    (fun x j => x.markPower (p ^ j) p) x

@[simp] theorem markRange_zero (x : PlaneCell) (p start : Nat) :
    markRange x p start 0 = x := rfl

theorem markRange_succ (x : PlaneCell) (p start count : Nat) :
    markRange x p start (count + 1) =
      markRange (x.markPower (p ^ start) p) p (start + 1) count := by
  simp [markRange, List.range'_succ]

theorem pow_ne_base {p j : Nat} (hp : 2 ≤ p) (hj : 2 ≤ j) : p ^ j ≠ p := by
  have hlt : p ^ 1 < p ^ j := Nat.pow_lt_pow_right (by omega) (by omega)
  intro heq
  rw [heq] at hlt
  have : p < p := by simpa only [Nat.pow_one] using hlt
  exact (Nat.lt_irrefl p this).elim

@[simp] theorem markPower_empty_first (p : Nat) (hp0 : p ≠ 0) :
    emptyPlaneCell.markPower p p = onePrimeCell p p 1 p := by
  simp [emptyPlaneCell, onePrimeCell, PlaneCell.markPower, hitP, installP,
    nextP, hitQ, installQ, nextQ, nextPowerProduct, eqBit, zeroBit,
    nonzeroBit, nonzeroProduct, hp0]

@[simp] theorem markPower_one_same (prod p pe pProd pow : Nat)
    (hp0 : p ≠ 0) (hpow : pow ≠ p) (hprod : prod ≠ 0)
    (hpProd : pProd ≠ 0) :
    (onePrimeCell prod p pe pProd).markPower pow p =
      onePrimeCell (prod * p) p (pe + 1) (pProd * p) := by
  simp [onePrimeCell, PlaneCell.markPower, hitP, installP, nextP, hitQ,
    installQ, nextQ, nextPowerProduct, eqBit, zeroBit, nonzeroBit,
    nonzeroProduct, hp0, hpow, hprod, hpProd]

@[simp] theorem markPower_one_new (prod p pe pProd q : Nat)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hpq : p ≠ q)
    (hprod : prod ≠ 0) (hpProd : pProd ≠ 0) :
    (onePrimeCell prod p pe pProd).markPower q q =
      twoPrimeCell (prod * q) p pe pProd q 1 q := by
  simp [onePrimeCell, twoPrimeCell, PlaneCell.markPower, hitP, installP,
    nextP, hitQ, installQ, nextQ, nextPowerProduct, eqBit, zeroBit,
    nonzeroBit, nonzeroProduct, hp0, hq0, hpq.symm, hprod, hpProd]

@[simp] theorem markPower_two_same (prod p pe pProd q qe qProd pow : Nat)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hpq : p ≠ q)
    (hpow : pow ≠ q) (hprod : prod ≠ 0) (hqProd : qProd ≠ 0) :
    (twoPrimeCell prod p pe pProd q qe qProd).markPower pow q =
      twoPrimeCell (prod * q) p pe pProd q (qe + 1) (qProd * q) := by
  simp [twoPrimeCell, PlaneCell.markPower, hitP, installP, nextP, hitQ,
    installQ, nextQ, nextPowerProduct, eqBit, zeroBit, nonzeroBit,
    nonzeroProduct, hp0, hq0, hpq.symm, hpow, hprod, hqProd]

@[simp] theorem markPower_two_new
    (prod p pe pProd q qe qProd r pow : Nat)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hpr : p ≠ r) (hqr : q ≠ r)
    (hprod : prod ≠ 0) :
    (twoPrimeCell prod p pe pProd q qe qProd).markPower pow r =
      twoPrimeCell (prod * r) p pe pProd q qe qProd := by
  simp [twoPrimeCell, PlaneCell.markPower, hitP, installP, nextP, hitQ,
    installQ, nextQ, nextPowerProduct, eqBit, zeroBit, nonzeroBit,
    nonzeroProduct, hp0, hq0, hpr.symm, hqr.symm, hprod]

theorem markRange_one_same (p start count prod pe pProd : Nat)
    (hp : 2 ≤ p) (hstart : 2 ≤ start)
    (hprod : prod ≠ 0) (hpProd : pProd ≠ 0) :
    markRange (onePrimeCell prod p pe pProd) p start count =
      onePrimeCell (prod * p ^ count) p (pe + count)
        (pProd * p ^ count) := by
  induction count generalizing start prod pe pProd with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = n.succ by rfl, markRange_succ]
      rw [markPower_one_same prod p pe pProd (p ^ start) (by omega)
        (pow_ne_base hp hstart) hprod hpProd]
      rw [ih (start := start + 1) (prod := prod * p) (pe := pe + 1)
        (pProd := pProd * p) (by omega) (Nat.mul_ne_zero hprod (by omega))
        (Nat.mul_ne_zero hpProd (by omega))]
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
        Nat.add_comm, Nat.add_left_comm]

theorem markRange_two_same (p q start count prod pe pProd qe qProd : Nat)
    (hp0 : p ≠ 0) (hq : 2 ≤ q) (hpq : p ≠ q)
    (hstart : 2 ≤ start) (hprod : prod ≠ 0) (hqProd : qProd ≠ 0) :
    markRange (twoPrimeCell prod p pe pProd q qe qProd) q start count =
      twoPrimeCell (prod * q ^ count) p pe pProd q (qe + count)
        (qProd * q ^ count) := by
  induction count generalizing start prod qe qProd with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = n.succ by rfl, markRange_succ]
      rw [markPower_two_same prod p pe pProd q qe qProd (q ^ start) hp0
        (by omega) hpq (pow_ne_base hq hstart) hprod hqProd]
      rw [ih (start := start + 1) (prod := prod * q) (qe := qe + 1)
        (qProd := qProd * q) (by omega) (Nat.mul_ne_zero hprod (by omega))
        (Nat.mul_ne_zero hqProd (by omega))]
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
        Nat.add_comm, Nat.add_left_comm]

theorem markRange_two_new (p q r start count prod pe pProd qe qProd : Nat)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hr0 : r ≠ 0)
    (hpr : p ≠ r) (hqr : q ≠ r)
    (hprod : prod ≠ 0) :
    markRange (twoPrimeCell prod p pe pProd q qe qProd) r start count =
      twoPrimeCell (prod * r ^ count) p pe pProd q qe qProd := by
  induction count generalizing start prod with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = n.succ by rfl, markRange_succ]
      rw [markPower_two_new prod p pe pProd q qe qProd r (r ^ start)
        hp0 hq0 hpr hqr hprod]
      rw [ih (start := start + 1) (prod := prod * r)
        (Nat.mul_ne_zero hprod hr0)]
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- All positive powers of the first distinct prime produce its canonical
one-prime physical cell. -/
theorem markRange_empty (p e : Nat) (hp : 2 ≤ p) :
    markRange emptyPlaneCell p 1 e =
      if e = 0 then emptyPlaneCell else onePrimeCell (p ^ e) p e (p ^ e) := by
  cases e with
  | zero => simp
  | succ n =>
      rw [show n + 1 = n.succ by rfl, markRange_succ]
      simp only [Nat.pow_one, markPower_empty_first p (by omega)]
      rw [markRange_one_same p 2 n p 1 p hp (by omega) (by omega) (by omega)]
      simp [Nat.pow_succ, Nat.mul_comm, Nat.add_comm]

/-- A positive block for the second distinct prime installs it on the first
power and then counts every remaining power. -/
theorem markRange_one_new (prod p pe pProd q e : Nat)
    (hp0 : p ≠ 0) (hq : 2 ≤ q) (hpq : p ≠ q)
    (hprod : prod ≠ 0) (hpProd : pProd ≠ 0) :
    markRange (onePrimeCell prod p pe pProd) q 1 e =
      if e = 0 then onePrimeCell prod p pe pProd
      else twoPrimeCell (prod * q ^ e) p pe pProd q e (q ^ e) := by
  cases e with
  | zero => simp
  | succ n =>
      rw [show n + 1 = n.succ by rfl, markRange_succ]
      simp only [Nat.pow_one,
        markPower_one_new prod p pe pProd q hp0 (by omega) hpq hprod hpProd]
      rw [markRange_two_same p q 2 n (prod * q) pe pProd 1 q hp0 hq hpq
        (by omega) (Nat.mul_ne_zero hprod (by omega)) (by omega)]
      simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.add_comm]

/-! ## Identification with the source-shaped segmented model -/

/-- The three reachable logical shapes of a physical plane cell.  Exact
prime-power products are retained on the physical side and erased by the
paper-facing `Cell`. -/
inductive CellRel : PlaneCell → Cell → Prop where
  | empty : CellRel emptyPlaneCell emptyCell
  | one (prod p pe : Nat) (hprod : prod ≠ 0) (hp : 2 ≤ p) :
      CellRel (onePrimeCell prod p pe (p ^ pe))
        ⟨prod, p, pe, 0, 0, 1⟩
  | two (prod p pe q qe : Nat) (hprod : prod ≠ 0)
      (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : p ≠ q) :
      CellRel (twoPrimeCell prod p pe (p ^ pe) q qe (q ^ qe))
        ⟨prod, p, pe, q, qe, 2⟩

/-- One complete block of power hits for a fresh active prime is exactly the
`RamareCombined100MSeg.markPrime` update. -/
theorem CellRel.markPrime {x : PlaneCell} {cell : Cell} (hrel : CellRel x cell)
    (n : Nat) (row : PrimeRow) (hactive : row.active = true)
    (hrow : 2 ≤ row.p) (hfreshP : cell.p ≠ row.p)
    (hfreshQ : cell.q ≠ row.p) :
    CellRel (markRange x row.p 1 (exponent32 row.p n))
      (RamareCombined100MSeg.markPrime n cell row) := by
  let e := exponent32 row.p n
  cases hrel with
  | empty =>
      by_cases he : e = 0
      · simpa [e, he, RamareCombined100MSeg.markPrime, emptyCell,
          hactive] using
          CellRel.empty
      · have hrange := markRange_empty row.p e hrow
        rw [if_neg he] at hrange
        rw [hrange]
        simpa [e, he, RamareCombined100MSeg.markPrime, emptyCell,
          hactive] using
          (CellRel.one (row.p ^ e) row.p e
            (Nat.ne_of_gt (Nat.pow_pos (by omega))) hrow)
  | one prod p pe hprod hp =>
      have hpFresh : p ≠ row.p := hfreshP
      by_cases he : e = 0
      · simpa [e, he, RamareCombined100MSeg.markPrime, hactive] using
          (CellRel.one prod p pe hprod hp)
      · have hrange := markRange_one_new prod p pe (p ^ pe) row.p e
          (by omega) hrow hpFresh hprod
          (Nat.ne_of_gt (Nat.pow_pos (by omega)))
        rw [if_neg he] at hrange
        rw [hrange]
        simpa [e, he, RamareCombined100MSeg.markPrime, hactive] using
          (CellRel.two (prod * row.p ^ e) p pe row.p e
            (Nat.mul_ne_zero hprod (Nat.ne_of_gt (Nat.pow_pos (by omega))))
            hp hrow
            hpFresh)
  | two prod p pe q qe hprod hp hq hpq =>
      have hpFresh : p ≠ row.p := hfreshP
      have hqFresh : q ≠ row.p := hfreshQ
      by_cases he : e = 0
      · simpa [e, he, RamareCombined100MSeg.markPrime, hactive] using
          (CellRel.two prod p pe q qe hprod hp hq hpq)
      · have hrange := markRange_two_new p q row.p 1 e prod pe (p ^ pe) qe
          (q ^ qe) (by omega) (by omega) (by omega) hpFresh hqFresh hprod
        rw [hrange]
        simpa [e, he, RamareCombined100MSeg.markPrime, hactive] using
          (CellRel.two (prod * row.p ^ e) p pe q qe
            (Nat.mul_ne_zero hprod (Nat.ne_of_gt (Nat.pow_pos (by omega))))
            hp hq hpq)

/-- Every source-recorded prime is fresh for every row still to process. -/
def FreshRows (cell : Cell) (rows : List PrimeRow) : Prop :=
  ∀ row ∈ rows, cell.p ≠ row.p ∧ cell.q ≠ row.p

def ValidRows (rows : List PrimeRow) : Prop :=
  ∀ row ∈ rows, row.active = true ∧ 2 ≤ row.p

def DistinctRows (rows : List PrimeRow) : Prop :=
  rows.Pairwise (fun a b => a.p ≠ b.p)

/-- The source update preserves freshness for the remaining distinct rows. -/
theorem FreshRows.markPrime (n : Nat) (cell : Cell) (head : PrimeRow)
    (tail : List PrimeRow)
    (hfresh : FreshRows cell (head :: tail))
    (hhead : ∀ row ∈ tail, head.p ≠ row.p)
    (hvalid : ValidRows tail) :
    FreshRows (RamareCombined100MSeg.markPrime n cell head) tail := by
  intro row hrow
  have hold := hfresh row (by simp [hrow])
  have hnew := hhead row hrow
  have hrow2 := (hvalid row hrow).2
  unfold RamareCombined100MSeg.markPrime
  by_cases ha : head.active = true
  · simp only [ha, Bool.not_true, Bool.false_or]
    by_cases he : exponent32 head.p n = 0
    · simp [he, hold]
    · simp only [he]
      by_cases hc0 : cell.count = 0
      · simpa [hc0] using
          (And.intro hnew (show (0 : Nat) ≠ row.p by omega))
      · by_cases hc1 : cell.count = 1
        · simp [hc1, hold, hnew]
        · simp [hc0, hc1, hold]
  · have hnot : !head.active = true := by
      cases h : head.active <;> simp_all
    have haf : head.active = false := by
      cases h : head.active <;> simp_all
    simp [haf, hold]

/-- Physical fold over all power hits of each table row. -/
def markRows (rows : List PrimeRow) (n : Nat) (x : PlaneCell) : PlaneCell :=
  rows.foldl (fun x row => markRange x row.p 1 (exponent32 row.p n)) x

/-- Row-wise induction from an arbitrary related, fresh prefix state. -/
theorem CellRel.markRows {x : PlaneCell} {cell : Cell} (hrel : CellRel x cell)
    (rows : List PrimeRow) (n : Nat) (hfresh : FreshRows cell rows)
    (hvalid : ValidRows rows) (hdistinct : DistinctRows rows) :
    CellRel (markRows rows n x) (rows.foldl (RamareCombined100MSeg.markPrime n) cell) := by
  induction rows generalizing x cell with
  | nil => simpa [markRows]
  | cons head tail ih =>
      have hheadValid := hvalid head (by simp)
      have htailValid : ValidRows tail := by
        intro row hrow
        exact hvalid row (by simp [hrow])
      rw [DistinctRows] at hdistinct
      have hpair := List.pairwise_cons.mp hdistinct
      have hheadDistinct := hpair.1
      have htailDistinct : DistinctRows tail := hpair.2
      have hheadFresh := hfresh head (by simp)
      have hrel' := hrel.markPrime n head hheadValid.1 hheadValid.2
        hheadFresh.1 hheadFresh.2
      have hfresh' := FreshRows.markPrime n cell head tail hfresh
        hheadDistinct htailValid
      change CellRel
        (LeanCompCert.Ports.RamareCombined100M.ShapeSieve.markRows tail n
          (markRange x head.p 1 (exponent32 head.p n)))
        (tail.foldl (RamareCombined100MSeg.markPrime n)
          (RamareCombined100MSeg.markPrime n cell head))
      exact ih hrel' hfresh' htailValid htailDistinct

/-- Starting from seven zero planes, the complete physical row fold refines
`markCell` exactly. -/
theorem markRows_refines_markCell (rows : List PrimeRow) (n : Nat)
    (hvalid : ValidRows rows) (hdistinct : DistinctRows rows) :
    CellRel (markRows rows n emptyPlaneCell) (markCell rows n) := by
  have hfresh : FreshRows emptyCell rows := by
    intro row hrow
    have hr := (hvalid row hrow).2
    simp [emptyCell]
    omega
  simpa [markCell] using
    CellRel.markRows CellRel.empty rows n hfresh hvalid hdistinct

/-! ## The physical prime table as source rows -/

def factorRow (p : Nat) : PrimeRow := ⟨p, true, 0, 0, 0, 0⟩

def factorRows (ps : List Nat) : List PrimeRow := ps.map factorRow

theorem factorRows_valid (ps : List Nat)
    (htwo : ∀ p ∈ ps, 2 ≤ p) : ValidRows (factorRows ps) := by
  intro row hrow
  simp only [factorRows, List.mem_map] at hrow
  obtain ⟨p, hp, rfl⟩ := hrow
  exact ⟨rfl, htwo p hp⟩

theorem factorRows_distinct (ps : List Nat) (hnodup : ps.Nodup) :
    DistinctRows (factorRows ps) := by
  rw [DistinctRows, factorRows]
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.map_cons]
      rw [List.pairwise_cons]
      constructor
      · intro row hrow
        simp only [List.mem_map] at hrow
        obtain ⟨q, hq, rfl⟩ := hrow
        simp only [factorRow]
        intro heq
        apply hnodup.1
        simpa [heq] using hq
      · exact ih hnodup.2

theorem markRows_factorRows_refines (ps : List Nat) (n : Nat)
    (htwo : ∀ p ∈ ps, 2 ≤ p) (hnodup : ps.Nodup) :
    CellRel (markRows (factorRows ps) n emptyPlaneCell)
      (markCell (factorRows ps) n) :=
  markRows_refines_markCell _ _ (factorRows_valid ps htwo)
    (factorRows_distinct ps hnodup)

theorem nodup_filter {α : Type} (f : α → Bool) :
    ∀ {xs : List α}, xs.Nodup → (xs.filter f).Nodup := by
  intro xs hxs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      by_cases hx : f x = true
      · simp [hx, List.nodup_cons, hxs.1, ih hxs.2]
      · simp [hx, ih hxs.2]

theorem trialPrimesBelow_two_le (bound p : Nat)
    (hp : p ∈ trialPrimesBelow bound) : 2 ≤ p := by
  have htest := (List.mem_filter.mp hp).2
  by_cases hsmall : p < 2
  · simp [trialPrime, hsmall] at htest
  · omega

theorem trialPrimesBelow_nodup (bound : Nat) :
    (trialPrimesBelow bound).Nodup := by
  exact nodup_filter trialPrime List.nodup_range

/-- The exact table constructor used by `Cfg.ofChain` satisfies the row-fold
side conditions without evaluating or trusting the old array sieve. -/
theorem ofChain_factorRows_refines (lo segLen segCount tableHi n : Nat) :
    CellRel
      (markRows (factorRows (Cfg.ofChain lo segLen segCount tableHi).table)
        n emptyPlaneCell)
      (markCell (factorRows (Cfg.ofChain lo segLen segCount tableHi).table) n) := by
  apply markRows_factorRows_refines
  · intro p hp
    exact trialPrimesBelow_two_le _ p hp
  · exact trialPrimesBelow_nodup _

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

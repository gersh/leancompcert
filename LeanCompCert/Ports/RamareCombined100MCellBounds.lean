import LeanCompCert.Ports.RamareCombined100MCursorMachine

/-!
# Word bounds for Ramaré seven-plane cells

The production marking loop represents integers at most `10^8` and uses
prime bases at most `10^4`.  This module packages the small mathematical
invariant needed by the emitted 43-instruction cell update and proves that it
implies every one of the update's explicit `u64` no-wrap obligations.

Keeping this implication outside the instruction proof is important: the
machine theorem continues to state its exact local requirements, while the
production loop induction carries only bounds with a direct paper-level
meaning.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Verified.Reflect

/-- Paper-scale bounds on one physical seven-plane cell.  Zero product
sentinels denote the empty product `1`, hence the use of `nonzeroProduct` in
the three product fields. -/
structure PlaneCellProductionBounds (x : PlaneCell) : Prop where
  prod : nonzeroProduct x.prod ≤ 100000000
  p : x.p ≤ 100000000
  pe : x.pe ≤ 32
  pProd : nonzeroProduct x.pProd ≤ 100000000
  q : x.q ≤ 100000000
  qe : x.qe ≤ 32
  qProd : nonzeroProduct x.qProd ≤ 100000000

/-- Source-shaped bounds corresponding to the seven physical planes.  The
source record stores the empty product as `1`, and records prime-power
products intensionally as `p ^ pe` and `q ^ qe`. -/
structure CellProductionBounds (cell : RamareCombined100MSeg.Cell) : Prop where
  prod : cell.prod ≤ 100000000
  p : cell.p ≤ 100000000
  pe : cell.pe ≤ 32
  pProd : cell.p ^ cell.pe ≤ 100000000
  q : cell.q ≤ 100000000
  qe : cell.qe ≤ 32
  qProd : cell.q ^ cell.qe ≤ 100000000

/-- Number-relative source invariant.  All recorded products divide the
selected candidate, and the fixed physical exponent budget is explicit. -/
structure CellDivisorBounds (n : Nat)
    (cell : RamareCombined100MSeg.Cell) : Prop where
  prodDvd : cell.prod ∣ n
  p : cell.p ≤ n
  pe : cell.pe ≤ 32
  pProdDvd : cell.p ^ cell.pe ∣ n
  q : cell.q ≤ n
  qe : cell.qe ≤ 32
  qProdDvd : cell.q ^ cell.qe ∣ n

theorem exponent32_le (p n : Nat) :
    RamareCombined100MSeg.exponent32 p n ≤ 32 := by
  rw [exponent32_eq_powerHitExponents_length]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- The last power counted by the finite 32-event source counter really
divides the selected candidate. -/
theorem pow_exponent32_dvd (p n : Nat) :
    p ^ RamareCombined100MSeg.exponent32 p n ∣ n := by
  let hits := powerHitExponents p n 1 32
  have hlen : RamareCombined100MSeg.exponent32 p n = hits.length := by
    exact exponent32_eq_powerHitExponents_length p n
  by_cases hzero : hits.length = 0
  · rw [hlen, hzero]
    simp
  · let e := hits.length
    have he0 : e ≠ 0 := by simpa [e] using hzero
    have hmemRange : e ∈ List.range' 1 e := by
      apply List.mem_range'.mpr
      exact ⟨e - 1, by omega, by omega⟩
    have hshape := powerHitExponents_eq_range' p n 1 32
    change hits = List.range' 1 e at hshape
    have hmemHits : e ∈ hits := by
      rw [hshape]
      exact hmemRange
    have hdiv : p ^ e ∣ n := by
      exact decide_eq_true_eq.mp (List.mem_filter.mp hmemHits).2
    rw [hlen]
    exact hdiv

theorem emptyCell_divisorBounds (n : Nat) :
    CellDivisorBounds n RamareCombined100MSeg.emptyCell := by
  constructor <;> simp [RamareCombined100MSeg.emptyCell]

/-- A positive candidate turns divisor bounds into the fixed production
ceiling expected by the word-level cell theorem. -/
theorem CellDivisorBounds.productionBounds
    {n : Nat} {cell : RamareCombined100MSeg.Cell}
    (hn : 0 < n) (hN : n ≤ 100000000)
    (hcell : CellDivisorBounds n cell) : CellProductionBounds cell := by
  constructor
  · exact Nat.le_trans (Nat.le_of_dvd hn hcell.prodDvd) hN
  · exact Nat.le_trans hcell.p hN
  · exact hcell.pe
  · exact Nat.le_trans (Nat.le_of_dvd hn hcell.pProdDvd) hN
  · exact Nat.le_trans hcell.q hN
  · exact hcell.qe
  · exact Nat.le_trans (Nat.le_of_dvd hn hcell.qProdDvd) hN

/-- One source row preserves all candidate-relative bounds when its base is
coprime to the product accumulated from earlier rows.  For the production
table this side condition follows from distinct primality. -/
theorem CellDivisorBounds.markPrime
    {n : Nat} {cell : RamareCombined100MSeg.Cell}
    (hn : 0 < n)
    (hcell : CellDivisorBounds n cell)
    (row : RamareCombined100MSeg.PrimeRow)
    (hcoprime : cell.prod.Coprime row.p) :
    CellDivisorBounds n
      (RamareCombined100MSeg.markPrime n cell row) := by
  let e := RamareCombined100MSeg.exponent32 row.p n
  have he32 : e ≤ 32 := exponent32_le row.p n
  have heDvd : row.p ^ e ∣ n := pow_exponent32_dvd row.p n
  unfold RamareCombined100MSeg.markPrime
  change CellDivisorBounds n
    (if !row.active || e = 0 then cell
      else if cell.count = 0 then
        ⟨cell.prod * row.p ^ e, row.p, e, 0, 0, 1⟩
      else if cell.count = 1 then
        ⟨cell.prod * row.p ^ e, cell.p, cell.pe, row.p, e, 2⟩
      else
        ⟨cell.prod * row.p ^ e, cell.p, cell.pe, cell.q, cell.qe, 2⟩)
  by_cases hskip : !row.active || e = 0
  · simpa [hskip] using hcell
  · have he0 : e ≠ 0 := by
      intro he
      apply hskip
      simp [he]
    have hbasePow : row.p ∣ row.p ^ e := by
      have := Nat.pow_dvd_pow row.p (show 1 ≤ e by omega)
      simpa using this
    have hbaseDvd : row.p ∣ n := Nat.dvd_trans hbasePow heDvd
    have hbaseLe : row.p ≤ n := Nat.le_of_dvd hn hbaseDvd
    have hprodDvd : cell.prod * row.p ^ e ∣ n :=
      (hcoprime.pow_right e).mul_dvd_of_dvd_of_dvd hcell.prodDvd heDvd
    rw [if_neg hskip]
    by_cases hcount0 : cell.count = 0
    · rw [if_pos hcount0]
      constructor
      · exact hprodDvd
      · exact hbaseLe
      · exact he32
      · exact heDvd
      · simp
      · simp
      · simp
    · rw [if_neg hcount0]
      by_cases hcount1 : cell.count = 1
      · rw [if_pos hcount1]
        exact ⟨hprodDvd, hcell.p, hcell.pe, hcell.pProdDvd,
          hbaseLe, he32, heDvd⟩
      · rw [if_neg hcount1]
        exact ⟨hprodDvd, hcell.p, hcell.pe, hcell.pProdDvd,
          hcell.q, hcell.qe, hcell.qProdDvd⟩

def CoprimeRows (cell : RamareCombined100MSeg.Cell)
    (rows : List RamareCombined100MSeg.PrimeRow) : Prop :=
  ∀ row ∈ rows, cell.prod.Coprime row.p

def PairwiseCoprimeRows
    (rows : List RamareCombined100MSeg.PrimeRow) : Prop :=
  rows.Pairwise (fun a b => a.p.Coprime b.p)

theorem CoprimeRows.emptyCell
    (rows : List RamareCombined100MSeg.PrimeRow) :
    CoprimeRows RamareCombined100MSeg.emptyCell rows := by
  intro row hrow
  simp [RamareCombined100MSeg.emptyCell]

/-- After processing one row, the accumulated product remains coprime to
every pairwise-coprime row still to process. -/
theorem CoprimeRows.markPrime
    (n : Nat) (cell : RamareCombined100MSeg.Cell)
    (head : RamareCombined100MSeg.PrimeRow)
    (tail : List RamareCombined100MSeg.PrimeRow)
    (hrows : CoprimeRows cell (head :: tail))
    (hhead : ∀ row ∈ tail, head.p.Coprime row.p) :
    CoprimeRows (RamareCombined100MSeg.markPrime n cell head) tail := by
  intro row hrow
  have hold : cell.prod.Coprime row.p := hrows row (by simp [hrow])
  have hnew : head.p.Coprime row.p := hhead row hrow
  let e := RamareCombined100MSeg.exponent32 head.p n
  unfold RamareCombined100MSeg.markPrime
  change (if !head.active || e = 0 then cell
    else if cell.count = 0 then
      ⟨cell.prod * head.p ^ e, head.p, e, 0, 0, 1⟩
    else if cell.count = 1 then
      ⟨cell.prod * head.p ^ e, cell.p, cell.pe, head.p, e, 2⟩
    else
      ⟨cell.prod * head.p ^ e, cell.p, cell.pe, cell.q, cell.qe, 2⟩).prod.Coprime
      row.p
  by_cases hskip : !head.active || e = 0
  · simpa [hskip] using hold
  · have hmul : (cell.prod * head.p ^ e).Coprime row.p :=
      Nat.Coprime.mul_left hold (hnew.pow_left e)
    rw [if_neg hskip]
    by_cases hcount0 : cell.count = 0
    · rw [if_pos hcount0]
      exact hmul
    · rw [if_neg hcount0]
      by_cases hcount1 : cell.count = 1
      · rw [if_pos hcount1]
        exact hmul
      · rw [if_neg hcount1]
        exact hmul

/-- A complete source row fold is candidate-bounded whenever its bases are
pairwise coprime.  No execution or production-sized reduction occurs in this
proof. -/
theorem markCell_divisorBounds
    (rows : List RamareCombined100MSeg.PrimeRow) (n : Nat)
    (hn : 0 < n) (hpair : PairwiseCoprimeRows rows) :
    CellDivisorBounds n (RamareCombined100MSeg.markCell rows n) := by
  have go : ∀ (todo : List RamareCombined100MSeg.PrimeRow)
      (cell : RamareCombined100MSeg.Cell),
      CellDivisorBounds n cell → CoprimeRows cell todo →
      PairwiseCoprimeRows todo →
      CellDivisorBounds n
        (todo.foldl (RamareCombined100MSeg.markPrime n) cell) := by
    intro todo
    induction todo with
    | nil =>
        intro cell hcell hcoprime htodo
        simpa using hcell
    | cons head tail ih =>
        intro cell hcell hcoprime htodo
        rw [PairwiseCoprimeRows, List.pairwise_cons] at htodo
        simp only [List.foldl_cons]
        apply ih
        · exact hcell.markPrime hn head (hcoprime head (by simp))
        · exact hcoprime.markPrime n cell head tail htodo.1
        · exact htodo.2
  unfold RamareCombined100MSeg.markCell
  exact go rows RamareCombined100MSeg.emptyCell
    (emptyCell_divisorBounds n) (CoprimeRows.emptyCell rows) hpair

theorem markCell_productionBounds
    (rows : List RamareCombined100MSeg.PrimeRow) (n : Nat)
    (hn : 0 < n) (hN : n ≤ 100000000)
    (hpair : PairwiseCoprimeRows rows) :
    CellProductionBounds (RamareCombined100MSeg.markCell rows n) :=
  (markCell_divisorBounds rows n hn hpair).productionBounds hn hN

/-! ## Symbolic coprimality of the trial table -/

theorem trialPrime_two_le {n : Nat} (hprime : trialPrime n = true) :
    2 ≤ n := by
  unfold trialPrime at hprime
  by_cases hsmall : n < 2
  · simp [hsmall] at hprime
  · omega

/-- The trial predicate rejects every proper divisor no larger than the
integer square root. -/
theorem trialPrime_not_dvd {n d : Nat}
    (hprime : trialPrime n = true) (hd : 2 ≤ d)
    (hroot : d ≤ Nat.sqrt n) (hproper : d ≠ n) : ¬d ∣ n := by
  intro hdvd
  have hn2 := trialPrime_two_le hprime
  unfold trialPrime at hprime
  rw [if_neg (by omega)] at hprime
  have hall := List.all_eq_true.mp hprime d (by
    rw [List.mem_range]
    omega)
  have hmod : n % d = 0 := Nat.mod_eq_zero_of_dvd hdvd
  simp [show ¬d < 2 by omega, hmod] at hall
  exact hproper hall.symm

theorem trialPrime_coprime_of_lt {a b : Nat}
    (ha : trialPrime a = true) (hb : trialPrime b = true)
    (hab : a < b) : a.Coprime b := by
  have ha2 := trialPrime_two_le ha
  have hb2 := trialPrime_two_le hb
  rw [Nat.coprime_iff_gcd_eq_one]
  let g := a.gcd b
  have hgPos : 0 < g := by
    exact Nat.gcd_pos_of_pos_left b (by omega)
  by_cases hgOne : g = 1
  · simpa [g] using hgOne
  · exfalso
    have hg2 : 2 ≤ g := by omega
    have hgDvdA : g ∣ a := Nat.gcd_dvd_left a b
    have hgDvdB : g ∣ b := Nat.gcd_dvd_right a b
    have hgLeA : g ≤ a := Nat.gcd_le_left b (by omega)
    have hgLtB : g < b := Nat.lt_of_le_of_lt hgLeA hab
    obtain ⟨q, hbEq⟩ := hgDvdB
    have hqPos : 0 < q := by
      by_cases hq0 : q = 0
      · subst q
        simp at hbEq
        omega
      · exact Nat.pos_of_ne_zero hq0
    have hq2 : 2 ≤ q := by
      by_cases hqTwo : 2 ≤ q
      · exact hqTwo
      · have hqOne : q = 1 := by omega
        subst q
        simp at hbEq
        omega
    have hqLtB : q < b := by
      have hlt : 1 * q < g * q :=
        Nat.mul_lt_mul_of_pos_right (by omega) hqPos
      simpa [hbEq] using hlt
    by_cases hgRoot : g ≤ Nat.sqrt b
    · exact trialPrime_not_dvd hb hg2 hgRoot (by omega) ⟨q, hbEq⟩
    · have hqRoot : q ≤ Nat.sqrt b := by
        by_cases hqRoot : q ≤ Nat.sqrt b
        · exact hqRoot
        · exfalso
          have hmul : (Nat.sqrt b + 1) * (Nat.sqrt b + 1) ≤ g * q :=
            Nat.mul_le_mul (by omega) (by omega)
          have hsqrt := Nat.lt_succ_sqrt b
          have hmulB : (Nat.sqrt b + 1) * (Nat.sqrt b + 1) ≤ b :=
            calc
              _ ≤ g * q := hmul
              _ = b := hbEq.symm
          have hsqrt' : b < (Nat.sqrt b + 1) * (Nat.sqrt b + 1) := by
            simpa [Nat.succ_eq_add_one] using hsqrt
          omega
      have hqDvdB : q ∣ b := ⟨g, by simpa [Nat.mul_comm] using hbEq⟩
      exact trialPrime_not_dvd hb hq2 hqRoot (by omega) hqDvdB

/-- Two distinct accepted trial-table entries are coprime.  This avoids the
21-GiB kernel reduction needed to check all 1.5 million pairs directly. -/
theorem trialPrime_coprime {a b : Nat}
    (ha : trialPrime a = true) (hb : trialPrime b = true)
    (hne : a ≠ b) : a.Coprime b := by
  rcases Nat.lt_or_lt_of_ne hne with hab | hba
  · exact trialPrime_coprime_of_lt ha hb hab
  · exact Nat.coprime_comm.mp (trialPrime_coprime_of_lt hb ha hba)

theorem pairwiseCoprime_of_trialPrime
    (ps : List Nat) (hnodup : ps.Nodup)
    (hprime : ∀ p ∈ ps, trialPrime p = true) :
    ps.Pairwise Nat.Coprime := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.pairwise_cons]
      constructor
      · intro q hq
        exact trialPrime_coprime
          (hprime p (by simp)) (hprime q (by simp [hq]))
          (by intro hpq; subst q; exact hnodup.1 hq)
      · exact ih hnodup.2 (fun q hq => hprime q (by simp [hq]))

theorem trialPrimesBelow_pairwiseCoprime (bound : Nat) :
    (trialPrimesBelow bound).Pairwise Nat.Coprime := by
  apply pairwiseCoprime_of_trialPrime
  · exact trialPrimesBelow_nodup bound
  · intro p hp
    exact (List.mem_filter.mp hp).2

theorem factorRows_trialPrimesBelow_pairwiseCoprime (bound : Nat) :
    PairwiseCoprimeRows (factorRows (trialPrimesBelow bound)) := by
  unfold PairwiseCoprimeRows factorRows
  exact (trialPrimesBelow_pairwiseCoprime bound).map factorRow
    (by intro a b hab; simpa [factorRow] using hab)

theorem ofChain_factorRows_pairwiseCoprime
    (lo segLen segCount tableHi : Nat) :
    PairwiseCoprimeRows
      (factorRows (Cfg.ofChain lo segLen segCount tableHi).table) := by
  simpa [Cfg.ofChain] using
    factorRows_trialPrimesBelow_pairwiseCoprime (Nat.sqrt tableHi + 1)

/-- Closed-form source bounds for every positive candidate in an `ofChain`
window at or below the production ceiling. -/
theorem ofChain_markCell_productionBounds
    (lo segLen segCount tableHi n : Nat)
    (hn : 0 < n) (hN : n ≤ 100000000) :
    CellProductionBounds
      (RamareCombined100MSeg.markCell
        (factorRows (Cfg.ofChain lo segLen segCount tableHi).table) n) :=
  markCell_productionBounds _ n hn hN
    (ofChain_factorRows_pairwiseCoprime lo segLen segCount tableHi)

/-- Replacing the raw zero sentinel by the mathematical empty product
preserves every production-scale upper bound. -/
theorem nonzeroProduct_le_production {x : Nat}
    (hx : x ≤ 100000000) : nonzeroProduct x ≤ 100000000 := by
  by_cases hzero : x = 0
  · simp [nonzeroProduct, zeroBit, hzero]
  · simpa [nonzeroProduct, zeroBit, hzero] using hx

/-- The empty physical cell satisfies the production invariant. -/
theorem emptyPlaneCell_productionBounds :
    PlaneCellProductionBounds emptyPlaneCell := by
  constructor <;> decide

/-- The exact logical relation between a source cell and its seven physical
planes transfers the paper-scale source bounds to the machine-facing
invariant.  In particular, this proves that the zero sentinels in absent
prime slots denote the bounded value `1`; it is not an extra representation
assumption. -/
theorem CellRel.productionBounds {x : PlaneCell}
    {cell : RamareCombined100MSeg.Cell} (hrel : CellRel x cell)
    (hcell : CellProductionBounds cell) :
    PlaneCellProductionBounds x := by
  cases hrel with
  | empty =>
      exact emptyPlaneCell_productionBounds
  | one prod p pe hprod hp =>
      constructor
      · simpa [onePrimeCell, nonzeroProduct, zeroBit, hprod] using hcell.prod
      · simpa [onePrimeCell] using hcell.p
      · simpa [onePrimeCell] using hcell.pe
      · have hp0 : p ≠ 0 := by omega
        simpa [onePrimeCell, nonzeroProduct, zeroBit, hp0] using hcell.pProd
      · simpa [onePrimeCell] using hcell.q
      · simpa [onePrimeCell] using hcell.qe
      · simpa [onePrimeCell, nonzeroProduct, zeroBit] using hcell.qProd
  | two prod p pe q qe hprod hp hq hpq =>
      constructor
      · simpa [twoPrimeCell, nonzeroProduct, zeroBit, hprod] using hcell.prod
      · simpa [twoPrimeCell] using hcell.p
      · simpa [twoPrimeCell] using hcell.pe
      · have hp0 : p ≠ 0 := by omega
        simpa [twoPrimeCell, nonzeroProduct, zeroBit, hp0] using hcell.pProd
      · simpa [twoPrimeCell] using hcell.q
      · simpa [twoPrimeCell] using hcell.qe
      · have hq0 : q ≠ 0 := by omega
        simpa [twoPrimeCell, nonzeroProduct, zeroBit, hq0] using hcell.qProd

/-- Exact post-update bounds are enough to re-establish the compact physical
invariant after one logical cell update.  Later phase induction supplies
these seven mathematical inequalities from divisibility by the selected
candidate; this lemma keeps sentinel normalization out of that induction. -/
theorem PlaneCellProductionBounds.markPower_of_next
    (x : PlaneCell) (pow base : Nat)
    (hprod : nonzeroProduct x.prod * base ≤ 100000000)
    (hp : nextP pow base x.p ≤ 100000000)
    (hpe : x.pe + hitP pow base x.p ≤ 32)
    (hpProd : nextPowerProduct (hitP pow base x.p) x.pProd base ≤
      100000000)
    (hq : nextQ pow base x.p x.q ≤ 100000000)
    (hqe : x.qe + hitQ pow base x.p x.q ≤ 32)
    (hqProd : nextPowerProduct (hitQ pow base x.p x.q) x.qProd base ≤
      100000000) :
    PlaneCellProductionBounds (x.markPower pow base) := by
  simp only [PlaneCell.markPower]
  constructor
  · exact nonzeroProduct_le_production hprod
  · exact hp
  · exact hpe
  · exact nonzeroProduct_le_production hpProd
  · exact hq
  · exact hqe
  · exact nonzeroProduct_le_production hqProd

/-- The sentinel-normalized product is positive. -/
theorem nonzeroProduct_pos (x : Nat) : 0 < nonzeroProduct x := by
  by_cases hzero : x = 0
  · simp [nonzeroProduct, zeroBit, hzero]
  · simpa [nonzeroProduct, zeroBit, hzero] using Nat.pos_of_ne_zero hzero

theorem nonzeroProduct_eq_self {x : Nat} (hx : x ≠ 0) :
    nonzeroProduct x = x := by
  simp only [nonzeroProduct, zeroBit, if_neg hx, Nat.add_zero]

/-- Installing a first prime never decreases its raw plane. -/
theorem le_nextP (pow base p : Nat) : p ≤ nextP pow base p := by
  simp only [nextP, installP, eqBit, zeroBit]
  split <;> split <;> omega

/-- Installing a second prime never decreases its raw plane. -/
theorem le_nextQ (pow base p q : Nat) : q ≤ nextQ pow base p q := by
  simp only [nextQ, installQ, eqBit, nonzeroBit, zeroBit]
  split <;> split <;> split <;> omega

/-- A hit extends an exact prime-power product by a positive base; a miss
leaves it unchanged.  Either way the normalized mathematical product is
monotone. -/
theorem nonzeroProduct_le_nextPowerProduct
    (hit raw base : Nat) (hhit : hit ≤ 1) (hbase : 1 ≤ base) :
    nonzeroProduct raw ≤
      nonzeroProduct (nextPowerProduct hit raw base) := by
  have hhitCases : hit = 0 ∨ hit = 1 := by omega
  rcases hhitCases with rfl | rfl
  · simp [nextPowerProduct]
  · have hnorm0 : nonzeroProduct raw ≠ 0 :=
      Nat.ne_of_gt (nonzeroProduct_pos raw)
    have hmul0 : nonzeroProduct raw * base ≠ 0 :=
      Nat.mul_ne_zero hnorm0 (by omega)
    have hout : nonzeroProduct (nonzeroProduct raw * base) =
        nonzeroProduct raw * base := by
      exact nonzeroProduct_eq_self hmul0
    rw [show nextPowerProduct 1 raw base = nonzeroProduct raw * base by
      simp [nextPowerProduct], hout]
    exact Nat.le_mul_of_pos_right (nonzeroProduct raw) (by omega)

/-- Production bounds can be read backwards across one positive-base cell
update.  This is the key induction direction for the emitted phase loop: its
closed final cell is source-bounded, so every earlier prefix cell is bounded
and therefore satisfies the next machine update's word precondition. -/
theorem PlaneCellProductionBounds.of_markPower
    {x : PlaneCell} {pow base : Nat}
    (hbase : 1 ≤ base)
    (hnext : PlaneCellProductionBounds (x.markPower pow base)) :
    PlaneCellProductionBounds x := by
  constructor
  · have hnorm0 : nonzeroProduct x.prod ≠ 0 :=
      Nat.ne_of_gt (nonzeroProduct_pos x.prod)
    have hmul0 : nonzeroProduct x.prod * base ≠ 0 :=
      Nat.mul_ne_zero hnorm0 (by omega)
    have hmulBound := hnext.prod
    change nonzeroProduct (nonzeroProduct x.prod * base) ≤ 100000000 at hmulBound
    rw [show nonzeroProduct (nonzeroProduct x.prod * base) =
        nonzeroProduct x.prod * base by
      exact nonzeroProduct_eq_self hmul0] at hmulBound
    exact Nat.le_trans
      (Nat.le_mul_of_pos_right (nonzeroProduct x.prod) (by omega))
      hmulBound
  · have hpNext := hnext.p
    change nextP pow base x.p ≤ 100000000 at hpNext
    exact Nat.le_trans (le_nextP pow base x.p) hpNext
  · have hpeNext := hnext.pe
    change x.pe + hitP pow base x.p ≤ 32 at hpeNext
    exact Nat.le_trans (Nat.le_add_right x.pe _) hpeNext
  · exact Nat.le_trans
      (nonzeroProduct_le_nextPowerProduct _ _ _
        (hitP_le_one pow base x.p (by omega)) hbase)
      (by
        have hppNext := hnext.pProd
        change nonzeroProduct
          (nextPowerProduct (hitP pow base x.p) x.pProd base) ≤
            100000000 at hppNext
        exact hppNext)
  · have hqNext := hnext.q
    change nextQ pow base x.p x.q ≤ 100000000 at hqNext
    exact Nat.le_trans (le_nextQ pow base x.p x.q) hqNext
  · have hqeNext := hnext.qe
    change x.qe + hitQ pow base x.p x.q ≤ 32 at hqeNext
    exact Nat.le_trans (Nat.le_add_right x.qe _) hqeNext
  · exact Nat.le_trans
      (nonzeroProduct_le_nextPowerProduct _ _ _
        (hitQ_le_one pow base x.p x.q (by omega)) hbase)
      (by
        have hqpNext := hnext.qProd
        change nonzeroProduct
          (nextPowerProduct (hitQ pow base x.p x.q) x.qProd base) ≤
            100000000 at hqpNext
        exact hqpNext)

/-- Read production bounds backwards through an arbitrary finite event block.
Only the selected offset changes; every other event is an array frame. -/
theorem PlaneCellProductionBounds.of_planeEventCellFold
    (i base : Nat) (events : List (Nat × Nat)) (x : PlaneCell)
    (hbase : 1 ≤ base)
    (hfinal : PlaneCellProductionBounds
      (planeEventCellFold i base events x)) :
    PlaneCellProductionBounds x := by
  induction events generalizing x with
  | nil => simpa [planeEventCellFold] using hfinal
  | cons event events ih =>
      simp only [planeEventCellFold, List.foldl_cons] at hfinal
      have hstep := ih
        (if event.1 = i then x.markPower event.2 base else x) hfinal
      by_cases hselected : event.1 = i
      · rw [if_pos hselected] at hstep
        exact PlaneCellProductionBounds.of_markPower hbase hstep
      · simpa [hselected] using hstep

/-- Specialization to one complete arithmetic-progression cursor block. -/
theorem PlaneCellProductionBounds.of_cursorPowerFold
    (segLen w i pow base : Nat) (x : PlaneCell)
    (hbase : 1 ≤ base)
    (hfinal : PlaneCellProductionBounds
      (cursorPowerFold segLen w i pow base x)) :
    PlaneCellProductionBounds x :=
  PlaneCellProductionBounds.of_planeEventCellFold
    i base (powerCursorEvents segLen w pow) x hbase hfinal

/-- At production scale, the compact mathematical cell invariant implies all
twelve local no-wrap premises required by the emitted cell-update theorem.

The largest product admitted here is `10^8 * 10^4 = 10^12`, far below
`2^64`; exponent counters grow by at most one on a single power event. -/
theorem PlaneCellMarkPre.of_productionBounds
    {pow base : Nat} {x : PlaneCell}
    (hx : PlaneCellProductionBounds x)
    (hbase0 : base ≠ 0) (hbase : base ≤ 10000) :
    PlaneCellMarkPre pow base x := by
  have hprodMul : nonzeroProduct x.prod * base ≤
      100000000 * 10000 := Nat.mul_le_mul hx.prod hbase
  have hpProdMul : nonzeroProduct x.pProd * base ≤
      100000000 * 10000 := Nat.mul_le_mul hx.pProd hbase
  have hqProdMul : nonzeroProduct x.qProd * base ≤
      100000000 * 10000 := Nat.mul_le_mul hx.qProd hbase
  have hhitP : hitP pow base x.p ≤ 1 := hitP_le_one _ _ _ hbase0
  have hhitQ : hitQ pow base x.p x.q ≤ 1 :=
    hitQ_le_one _ _ _ _ hbase0
  constructor
  · exact hbase0
  · exact Nat.lt_of_le_of_lt hbase (by decide)
  · exact Nat.lt_of_le_of_lt hx.prod (by decide)
  · exact Nat.lt_of_le_of_lt hprodMul (by decide)
  · exact Nat.lt_of_le_of_lt hx.p (by decide)
  · exact Nat.lt_of_le_of_lt (Nat.add_le_add hx.pe hhitP) (by decide)
  · exact Nat.lt_of_le_of_lt hx.pProd (by decide)
  · exact Nat.lt_of_le_of_lt hpProdMul (by decide)
  · exact Nat.lt_of_le_of_lt hx.q (by decide)
  · exact Nat.lt_of_le_of_lt (Nat.add_le_add hx.qe hhitQ) (by decide)
  · exact Nat.lt_of_le_of_lt hx.qProd (by decide)
  · exact Nat.lt_of_le_of_lt hqProdMul (by decide)

/-- A production-bounded selected cell and a production table base discharge
the cell premise in `Cfg.markCellPrefixAdvance_run` directly. -/
theorem planeCellMarkPre_of_production
    (pow base : Nat) (x : PlaneCell)
    (hx : PlaneCellProductionBounds x)
    (hbase : 2 ≤ base) (hbaseMax : base ≤ 10000) :
    PlaneCellMarkPre pow base x :=
  PlaneCellMarkPre.of_productionBounds hx (by omega) hbaseMax

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

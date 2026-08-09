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

/-- The empty physical cell satisfies the production invariant. -/
theorem emptyPlaneCell_productionBounds :
    PlaneCellProductionBounds emptyPlaneCell := by
  constructor <;> decide

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

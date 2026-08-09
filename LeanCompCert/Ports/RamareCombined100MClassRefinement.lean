import LeanCompCert.Ports.RamareCombined100MProductionInit

/-!
# Classifier refinement for the Ramaré combined 100-million sweep

The marking proof identifies each seven-plane machine cell with the
source-shaped segmented-factorisation cell.  This file starts the next
refinement layer: it gives the classifier's register arithmetic a small pure
model and identifies that model with `RamareCombined100MSeg.finish`.

Keeping the decoder separate from the instruction semantics lets the machine
proof compose the already-split classifier stages without normalizing the
whole production loop or even the whole classifier in one kernel term.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100MSeg

/-- Pure form of the values written to shape registers `100` through `105`.
It deliberately uses the same zero sentinels and selector arithmetic as the
emitted classifier. -/
def decodePlaneCell (n : Nat) (x : PlaneCell) : Shape :=
  let hasP := nonzeroBit x.p
  let noP := zeroBit x.p
  let rest := hasP * (n / nonzeroProduct x.pProd) + noP
  let restMore := notOneBit rest
  let noQ := zeroBit x.q
  let hasQ := nonzeroBit x.q
  let largeQ := restMore * noQ
  let markedQ := restMore * hasQ
  { p := hasP * x.p + noP * n
    pExp := hasP * x.pe + noP
    rest := rest
    q := markedQ * x.q + largeQ * rest
    qExp := markedQ * x.qe + largeQ
    tail := markedQ * (rest / nonzeroProduct x.qProd) +
      (1 - markedQ) }

/-- Source facts erased by `CellRel` but retained by an actually reachable
row fold.  Divisibility makes the one-prime `prod = n` test agree with the
machine's `rest = 1` test.  The last field rules out the selector-degenerate
two-prime case. -/
structure CellClassifyPre (n : Nat) (cell : Cell) : Prop where
  prodDvd : cell.prod ∣ n
  oneProd : cell.count = 1 -> cell.prod = cell.p ^ cell.pe
  twoRest : cell.count = 2 -> n / (cell.p ^ cell.pe) ≠ 1

/-- Structural facts established by the source row fold.  Besides explaining
the saturated count, this records enough multiplicative structure to rule out
the classifier's degenerate `rest = 1` branch for a two-prime cell. -/
structure CellFactorShape (cell : Cell) : Prop where
  count_le : cell.count ≤ 2
  emptyProd : cell.count = 0 -> cell.prod = 1
  one : cell.count = 1 ->
    cell.prod = cell.p ^ cell.pe ∧ 2 ≤ cell.p ∧ 0 < cell.pe
  two : cell.count = 2 ->
    2 ≤ cell.p ∧ 2 ≤ cell.q ∧ 0 < cell.qe ∧
      cell.p ^ cell.pe * cell.q ^ cell.qe ∣ cell.prod

theorem emptyCell_factorShape : CellFactorShape emptyCell := by
  constructor <;> simp [emptyCell]

/-- One valid row preserves the structural factor shape.  The proof is over
the source record only; it does not execute any emitted cursor rounds. -/
theorem CellFactorShape.markPrime {cell : Cell}
    (hcell : CellFactorShape cell) (n : Nat) (row : PrimeRow)
    (hrow : 2 ≤ row.p) :
    CellFactorShape (markPrime n cell row) := by
  let e := exponent32 row.p n
  unfold RamareCombined100MSeg.markPrime
  change CellFactorShape
    (if !row.active || e = 0 then cell
      else if cell.count = 0 then
        ⟨cell.prod * row.p ^ e, row.p, e, 0, 0, 1⟩
      else if cell.count = 1 then
        ⟨cell.prod * row.p ^ e, cell.p, cell.pe, row.p, e, 2⟩
      else
        ⟨cell.prod * row.p ^ e, cell.p, cell.pe, cell.q, cell.qe, 2⟩)
  by_cases hskip : !row.active || e = 0
  · simpa [hskip] using hcell
  rw [if_neg hskip]
  have he : 0 < e := by
    have : e ≠ 0 := by
      intro hz
      apply hskip
      simp [hz]
    omega
  by_cases hc0 : cell.count = 0
  · rw [if_pos hc0]
    have hprod : cell.prod = 1 := hcell.emptyProd hc0
    constructor
    · simp
    · simp
    · intro _
      simp [hprod, hrow, he]
    · simp
  · rw [if_neg hc0]
    by_cases hc1 : cell.count = 1
    · rw [if_pos hc1]
      have hone := hcell.one hc1
      constructor
      · simp
      · simp
      · simp
      · intro _
        refine ⟨hone.2.1, hrow, he, ?_⟩
        rw [hone.1]
        simp
    · rw [if_neg hc1]
      have hcle : cell.count ≤ 2 := hcell.count_le
      have hc2 : cell.count = 2 := by omega
      have htwo := hcell.two hc2
      rcases htwo.2.2.2 with ⟨d, hd⟩
      constructor
      · simp
      · simp
      · simp
      · intro _
        exact ⟨htwo.1, htwo.2.1, htwo.2.2.1,
          ⟨d * row.p ^ e, by simp [hd, Nat.mul_assoc]⟩⟩

/-- The complete source row fold has the factor shape whenever every retained
row has a valid prime-sized base. -/
theorem markCell_factorShape (rows : List PrimeRow) (n : Nat)
    (hvalid : ValidRows rows) : CellFactorShape (markCell rows n) := by
  have go : ∀ (todo : List PrimeRow) (cell : Cell),
      CellFactorShape cell -> ValidRows todo ->
        CellFactorShape (todo.foldl (markPrime n) cell) := by
    intro todo
    induction todo with
    | nil =>
        intro cell hcell _
        simpa using hcell
    | cons head tail ih =>
        intro cell hcell hrows
        simp only [List.foldl_cons]
        apply ih
        · exact hcell.markPrime n head (hrows head (by simp)).2
        · intro row hrow
          exact hrows row (by simp [hrow])
  exact go rows emptyCell emptyCell_factorShape hvalid

/-- Divisor bounds plus the structural row-fold invariant discharge every
pure classifier side condition. -/
theorem markCell_classifyPre (rows : List PrimeRow) (n : Nat)
    (hn : 0 < n) (hvalid : ValidRows rows)
    (hpair : PairwiseCoprimeRows rows) :
    CellClassifyPre n (markCell rows n) := by
  let cell := markCell rows n
  have hdiv : CellDivisorBounds n cell :=
    markCell_divisorBounds rows n hn hpair
  have hshape : CellFactorShape cell :=
    markCell_factorShape rows n hvalid
  refine ⟨hdiv.prodDvd, ?_, ?_⟩
  · intro hone
    exact (hshape.one hone).1
  · intro htwo hquot
    have hs := hshape.two htwo
    have hboth : cell.p ^ cell.pe * cell.q ^ cell.qe ∣ n :=
      Nat.dvd_trans hs.2.2.2 hdiv.prodDvd
    have hfirstEq : cell.p ^ cell.pe = n :=
      Nat.eq_of_dvd_of_div_eq_one hdiv.pProdDvd hquot
    have hle : cell.p ^ cell.pe * cell.q ^ cell.qe ≤ n :=
      Nat.le_of_dvd hn hboth
    have hpPowPos : 0 < cell.p ^ cell.pe :=
      Nat.pow_pos (by omega)
    have hqPow : 2 ≤ cell.q ^ cell.qe := by
      calc
        2 ≤ cell.q := hs.2.1
        _ = cell.q ^ 1 := by simp
        _ ≤ cell.q ^ cell.qe :=
          Nat.pow_le_pow_right (by omega) (by omega)
    rw [hfirstEq] at hle hpPowPos
    have hdouble : n * 2 ≤ n * cell.q ^ cell.qe :=
      Nat.mul_le_mul_left n hqPow
    have hnDouble : n < n * 2 := by omega
    omega

/-- The pure physical decoder is the paper-facing segmented decoder on every
reachable logical cell.  The sole extra premise records the genuine
two-prime fact needed by the emitted selector: after removing the first prime
power, the residual is not one.  It will be discharged from the source row
fold's divisor invariant, rather than assumed by the final consumer. -/
theorem CellRel.decodePlaneCell_eq_finish {x : PlaneCell} {cell : Cell}
    (hrel : CellRel x cell) (n : Nat) (hpre : CellClassifyPre n cell) :
    decodePlaneCell n x = finish n cell := by
  cases hrel with
  | empty =>
      simp [decodePlaneCell, finish, emptyPlaneCell, emptyCell,
        zeroBit, nonzeroBit, nonzeroProduct, oneBit, notOneBit]
  | one prod p pe hprod hp =>
      have hp0 : p ≠ 0 := by omega
      have hpp0 : p ^ pe ≠ 0 :=
        Nat.ne_of_gt (Nat.pow_pos (by omega))
      have honeProd : prod = p ^ pe := hpre.oneProd rfl
      by_cases heq : prod = n
      · have hppEq : p ^ pe = n := honeProd.symm.trans heq
        have hn0 : n ≠ 0 := by simpa [hppEq] using hpp0
        have hdiv : n / n = 1 := Nat.div_self (Nat.pos_of_ne_zero hn0)
        simp [decodePlaneCell, finish, onePrimeCell, zeroBit, nonzeroBit,
          nonzeroProduct, oneBit, notOneBit, hp0, honeProd,
          hppEq, hn0, hdiv]
      · have hrest : n / prod ≠ 1 := by
          intro hquot
          exact heq (Nat.eq_of_dvd_of_div_eq_one hpre.prodDvd hquot)
        have hppNe : p ^ pe ≠ n := by
          intro h
          exact heq (honeProd.trans h)
        have hrest' : n / p ^ pe ≠ 1 := by
          simpa [← honeProd] using hrest
        simp [decodePlaneCell, finish, onePrimeCell, zeroBit, nonzeroBit,
          nonzeroProduct, oneBit, notOneBit, hp0, honeProd,
          hppNe, hrest']
  | two prod p pe q qe hprod hp hq hpq =>
      have hp0 : p ≠ 0 := by omega
      have hq0 : q ≠ 0 := by omega
      have hrest : n / p ^ pe ≠ 1 := by
        apply hpre.twoRest
        rfl
      simp [decodePlaneCell, finish, twoPrimeCell, zeroBit, nonzeroBit,
        nonzeroProduct, oneBit, notOneBit, hp0, hq0, hrest]

/-- A physical cell related to an actual finite row fold decodes to the exact
source `finish`; no reachability premise escapes to the consumer. -/
theorem CellRel.decodePlaneCell_markCell {x : PlaneCell}
    (rows : List PrimeRow) (n : Nat)
    (hrel : CellRel x (markCell rows n))
    (hn : 0 < n) (hvalid : ValidRows rows)
    (hpair : PairwiseCoprimeRows rows) :
    decodePlaneCell n x = finish n (markCell rows n) :=
  hrel.decodePlaneCell_eq_finish n
    (markCell_classifyPre rows n hn hvalid hpair)

/-! ## Scalar classifier execution -/

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun astep)
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.ArrayRegFrame (arun_frame)
open LeanCompCert.Verified.InstrBlock

/-- Read the stable six-register shape convention from a machine state. -/
def shapeRegs (s : AState) : Shape :=
  ⟨s.regs rShapeP, s.regs rShapePE, s.regs rShapeRest,
    s.regs rShapeQ, s.regs rShapeQE, s.regs rShapeTail⟩

/-- The shape-producing prefix of `classDecodeBody`.  Exact-product guards
and their counter commit follow this block but do not overwrite registers
`100` through `105`. -/
def Cfg.classShapeBody (_c : Cfg) :
    List LeanCompCert.Verified.ArrayState.AInstr :=
  lift (Cfg.classNormalizeBody ++ Cfg.classFirstShapeBody ++
    Cfg.classSecondFlagsBody ++ Cfg.classSecondShapeBody ++
    Cfg.classTailBody)

set_option maxRecDepth 10000 in
/-- The scalar classifier prefix implements `decodePlaneCell`.  All premises
are local word bounds; the production cell invariant supplies them with a
large margin. -/
theorem Cfg.classShapeBody_run (c : Cfg) (k : Nat) (s : AState)
    (n : Nat) (x : PlaneCell)
    (h132 : s.regs 132 = n)
    (h140 : s.regs 140 = x.prod) (h141 : s.regs 141 = x.p)
    (h142 : s.regs 142 = x.pe) (h143 : s.regs 143 = x.pProd)
    (h144 : s.regs 144 = x.q) (h145 : s.regs 145 = x.qe)
    (h146 : s.regs 146 = x.qProd)
    (hn : n < M) (hp : x.p < M) (hpe : x.pe < M)
    (hpp : nonzeroProduct x.pProd < M)
    (hq : x.q < M) (hqe : x.qe < M)
    (hqpp : nonzeroProduct x.qProd < M) :
    shapeRegs (arun k s c.classShapeBody) = decodePlaneCell n x := by
  have hquot : n / nonzeroProduct x.pProd < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
  have htailQuot :
      n / nonzeroProduct x.pProd / nonzeroProduct x.qProd < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hquot
  have hpProd0 : nonzeroProduct x.pProd ≠ 0 := by
    by_cases h : x.pProd = 0 <;>
      simp [nonzeroProduct, zeroBit, h]
  have hqProd0 : nonzeroProduct x.qProd ≠ 0 := by
    by_cases h : x.qProd = 0 <;>
      simp [nonzeroProduct, zeroBit, h]
  have hpProdMod : nonzeroProduct x.pProd % M = nonzeroProduct x.pProd :=
    Nat.mod_eq_of_lt hpp
  have hqProdMod : nonzeroProduct x.qProd % M = nonzeroProduct x.qProd :=
    Nat.mod_eq_of_lt hqpp
  have hpProdRaw :
      x.pProd + (if x.pProd = 0 then 1 else 0) =
        nonzeroProduct x.pProd := by
    simp [nonzeroProduct, zeroBit]
  have hqProdRaw :
      x.qProd + (if x.qProd = 0 then 1 else 0) =
        nonzeroProduct x.qProd := by
    simp [nonzeroProduct, zeroBit]
  have hquotMod :
      (n / nonzeroProduct x.pProd) % M =
        n / nonzeroProduct x.pProd := Nat.mod_eq_of_lt hquot
  have htailQuotMod :
      (n / nonzeroProduct x.pProd / nonzeroProduct x.qProd) % M =
        n / nonzeroProduct x.pProd / nonzeroProduct x.qProd :=
    Nat.mod_eq_of_lt htailQuot
  have honeM : 1 % M = 1 := by decide
  have hzeroM : (1 + (M - 1)) % M = 0 := by decide
  by_cases hp0 : x.p = 0 <;>
    by_cases hr : n / nonzeroProduct x.pProd = 1 <;>
      by_cases hq0 : x.q = 0 <;>
        simp [Cfg.classShapeBody, shapeRegs, decodePlaneCell, arun, astep,
          LeanCompCert.Verified.ArrayState.AState.writeReg,
          Cfg.classNormalizeBody, Cfg.classFirstShapeBody,
          Cfg.classSecondFlagsBody, Cfg.classSecondShapeBody,
          Cfg.classTailBody, sdest, sval, denoteOperand, denoteOp,
          rShapeP, rShapePE, rShapeRest, rShapeQ,
          rShapeQE, rShapeTail, zeroBit, nonzeroBit, oneBit,
          notOneBit, h132, h140, h141, h142, h143, h144, h145, h146,
          hn, hp, hpe, hq, hqe,
          hpProd0, hqProd0, hpProdMod, hqProdMod, hpProdRaw, hqProdRaw,
          hquotMod,
          htailQuotMod, honeM, hzeroM, hp0, hr, hq0,
          Nat.mod_eq_of_lt]

/-- The exact-product guards and counter commit following the shape prefix. -/
def Cfg.classGuardBody (_c : Cfg) :
    List LeanCompCert.Verified.ArrayState.AInstr :=
  lift (Cfg.classFirstGuardBody ++ Cfg.classSecondGuardBody ++
    Cfg.classGuardCommitBody)

theorem Cfg.classDecodeBody_split (c : Cfg) :
    lift Cfg.classDecodeBody = c.classShapeBody ++ c.classGuardBody := by
  simp [Cfg.classDecodeBody, Cfg.classShapeBody, Cfg.classGuardBody,
    LeanCompCert.Verified.ArrayScalarBlock.lift_append,
    List.append_assoc]

/-- The guard suffix observes but does not overwrite the six decoded shape
registers. -/
theorem Cfg.classDecodeBody_shapeRegs (c : Cfg) (k : Nat) (s : AState) :
    shapeRegs (arun k s (lift Cfg.classDecodeBody)) =
      shapeRegs (arun k s c.classShapeBody) := by
  let mid := arun k s c.classShapeBody
  have hp := arun_frame k rShapeP c.classGuardBody (by rfl) mid
  have hpe := arun_frame k rShapePE c.classGuardBody (by rfl) mid
  have hr := arun_frame k rShapeRest c.classGuardBody (by rfl) mid
  have hq := arun_frame k rShapeQ c.classGuardBody (by rfl) mid
  have hqe := arun_frame k rShapeQE c.classGuardBody (by rfl) mid
  have ht := arun_frame k rShapeTail c.classGuardBody (by rfl) mid
  rw [c.classDecodeBody_split,
    LeanCompCert.Verified.ArrayFoldBridge.arun_append]
  unfold shapeRegs
  rw [hp, hpe, hr, hq, hqe, ht]

/-- The emitted decode block computes the pure physical decoder. -/
theorem Cfg.classDecodeBody_run (c : Cfg) (k : Nat) (s : AState)
    (n : Nat) (x : PlaneCell)
    (h132 : s.regs 132 = n)
    (h140 : s.regs 140 = x.prod) (h141 : s.regs 141 = x.p)
    (h142 : s.regs 142 = x.pe) (h143 : s.regs 143 = x.pProd)
    (h144 : s.regs 144 = x.q) (h145 : s.regs 145 = x.qe)
    (h146 : s.regs 146 = x.qProd)
    (hn : n < M) (hp : x.p < M) (hpe : x.pe < M)
    (hpp : nonzeroProduct x.pProd < M)
    (hq : x.q < M) (hqe : x.qe < M)
    (hqpp : nonzeroProduct x.qProd < M) :
    shapeRegs (arun k s (lift Cfg.classDecodeBody)) =
      decodePlaneCell n x := by
  rw [c.classDecodeBody_shapeRegs]
  exact c.classShapeBody_run k s n x h132 h140 h141 h142 h143 h144
    h145 h146 hn hp hpe hpp hq hqe hqpp

/-- For an `ofChain` table, the actual emitted scalar decoder returns the
paper-facing `finish` record.  Validity, coprimality, reachability, and every
word bound are discharged by the finite table construction. -/
theorem ofChain_classDecodeBody_run
    (lo segLen segCount tableHi k : Nat) (s : AState)
    (n : Nat) (x : PlaneCell)
    (hrel : CellRel x
      (markCell
        (factorRows (Cfg.ofChain lo segLen segCount tableHi).table) n))
    (hn : 0 < n) (hN : n ≤ 100000000)
    (h132 : s.regs 132 = n)
    (h140 : s.regs 140 = x.prod) (h141 : s.regs 141 = x.p)
    (h142 : s.regs 142 = x.pe) (h143 : s.regs 143 = x.pProd)
    (h144 : s.regs 144 = x.q) (h145 : s.regs 145 = x.qe)
    (h146 : s.regs 146 = x.qProd) :
    shapeRegs (arun k s (lift Cfg.classDecodeBody)) =
      finish n
        (markCell
          (factorRows (Cfg.ofChain lo segLen segCount tableHi).table) n) := by
  let c := Cfg.ofChain lo segLen segCount tableHi
  let rows := factorRows c.table
  let cell := markCell rows n
  have hcell : CellProductionBounds cell :=
    ofChain_markCell_productionBounds lo segLen segCount tableHi n hn hN
  have hx : PlaneCellProductionBounds x := hrel.productionBounds hcell
  have hword : 100000000 < M := by decide
  have hrun := c.classDecodeBody_run k s n x h132 h140 h141 h142 h143
    h144 h145 h146
    (Nat.lt_of_le_of_lt hN hword)
    (Nat.lt_of_le_of_lt hx.p hword)
    (Nat.lt_of_le_of_lt hx.pe (by omega))
    (Nat.lt_of_le_of_lt hx.pProd hword)
    (Nat.lt_of_le_of_lt hx.q hword)
    (Nat.lt_of_le_of_lt hx.qe (by omega))
    (Nat.lt_of_le_of_lt hx.qProd hword)
  have hvalid : ValidRows rows := by
    apply factorRows_valid
    intro p hp
    exact trialPrimesBelow_two_le _ p hp
  have hpair : PairwiseCoprimeRows rows :=
    ofChain_factorRows_pairwiseCoprime lo segLen segCount tableHi
  have hpure : decodePlaneCell n x = finish n cell :=
    hrel.decodePlaneCell_markCell rows n hn hvalid hpair
  exact hrun.trans hpure

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

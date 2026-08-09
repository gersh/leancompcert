import LeanCompCert.Ports.RamareCombined100MClassRefinement

/-!
# Exact classifier guards for the Ramaré combined sweep

The scalar classifier already refines the six paper-facing shape fields.
This module retains the two exact-product guard facts as well, so a correctly
marked source cell is proved not to increment the public violation counter.
-/

namespace LeanCompCert.Ports.RamareCombined100M.ShapeSieve

open LeanCompCert.Ports.RamareCombined100M
open LeanCompCert.Ports.RamareCombined100MSeg
open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState (AState)
open LeanCompCert.Verified.ArrayFoldBridge (arun astep)
open LeanCompCert.Verified.ArrayScalarBlock (lift arun_lift)
open LeanCompCert.Verified.ArrayRegFrame (writes arun_frame)
open LeanCompCert.Verified.InstrBlock

/-- The first physical exact-product guard succeeds on every related source
cell with the finite row-fold divisor invariant. -/
theorem CellRel.decodePlaneCell_firstGuard_exact
    {x : PlaneCell} {cell : Cell} (hrel : CellRel x cell)
    (n : Nat) (hdiv : CellDivisorBounds n cell)
    (hpre : CellClassifyPre n cell) :
    (zeroBit x.p * n + nonzeroBit x.p * nonzeroProduct x.pProd) *
        (decodePlaneCell n x).rest = n := by
  cases hrel with
  | empty =>
      simp [emptyPlaneCell, decodePlaneCell, zeroBit,
        nonzeroBit, nonzeroProduct]
  | one prod p pe hprod hp =>
      have hp0 : p ≠ 0 := by omega
      have hcancel : p ^ pe * (n / p ^ pe) = n :=
        Nat.mul_div_cancel' hdiv.pProdDvd
      simpa [onePrimeCell, decodePlaneCell, zeroBit, nonzeroBit,
        nonzeroProduct, hp0] using hcancel
  | two prod p pe q qe hprod hp hq hpq =>
      have hp0 : p ≠ 0 := by omega
      have hcancel : p ^ pe * (n / p ^ pe) = n :=
        Nat.mul_div_cancel' hdiv.pProdDvd
      simpa [twoPrimeCell, decodePlaneCell, zeroBit, nonzeroBit,
        nonzeroProduct, hp0] using hcancel

/-- The two normalized prime-power products jointly divide the candidate on
every reachable source row-fold cell. -/
theorem CellRel.nonzeroProducts_mul_dvd
    {x : PlaneCell} {cell : Cell} (hrel : CellRel x cell)
    (n : Nat) (hdiv : CellDivisorBounds n cell)
    (hshape : CellFactorShape cell) :
    nonzeroProduct x.pProd * nonzeroProduct x.qProd ∣ n := by
  cases hrel with
  | empty =>
      simpa [emptyPlaneCell, nonzeroProduct, zeroBit] using
        (show 1 ∣ n by simp)
  | one prod p pe hprod hp =>
      have hpow0 : p ^ pe ≠ 0 :=
        Nat.ne_of_gt (Nat.pow_pos (by omega))
      have hpNorm : nonzeroProduct (p ^ pe) = p ^ pe := by
        unfold nonzeroProduct zeroBit
        rw [if_neg hpow0]
        omega
      have hzeroNorm : nonzeroProduct 0 = 1 := by decide
      simpa only [onePrimeCell, hpNorm, hzeroNorm, Nat.mul_one] using
        hdiv.pProdDvd
  | two prod p pe q qe hprod hp hq hpq =>
      have hpPow0 : p ^ pe ≠ 0 :=
        Nat.ne_of_gt (Nat.pow_pos (by omega))
      have hqPow0 : q ^ qe ≠ 0 :=
        Nat.ne_of_gt (Nat.pow_pos (by omega))
      have hpNorm : nonzeroProduct (p ^ pe) = p ^ pe := by
        unfold nonzeroProduct zeroBit
        rw [if_neg hpPow0]
        omega
      have hqNorm : nonzeroProduct (q ^ qe) = q ^ qe := by
        unfold nonzeroProduct zeroBit
        rw [if_neg hqPow0]
        omega
      have hboth : p ^ pe * q ^ qe ∣ prod :=
        (hshape.two rfl).2.2.2
      simpa only [twoPrimeCell, hpNorm, hqNorm] using
        Nat.dvd_trans hboth hdiv.prodDvd

/-- The second physical exact-product guard succeeds on every related source
cell with the finite row-fold factor-shape invariant. -/
theorem CellRel.decodePlaneCell_secondGuard_exact
    {x : PlaneCell} {cell : Cell} (hrel : CellRel x cell)
    (n : Nat) (hdiv : CellDivisorBounds n cell)
    (hshape : CellFactorShape cell) (hpre : CellClassifyPre n cell) :
    let decoded := decodePlaneCell n x
    (notOneBit decoded.rest * zeroBit x.q * decoded.rest +
        notOneBit decoded.rest * nonzeroBit x.q *
          nonzeroProduct x.qProd +
        oneBit decoded.rest) * decoded.tail = decoded.rest := by
  have hboth := hrel.nonzeroProducts_mul_dvd n hdiv hshape
  cases hrel with
  | empty =>
      simp [emptyPlaneCell, decodePlaneCell, zeroBit, nonzeroBit,
        nonzeroProduct, oneBit, notOneBit]
  | one prod p pe hprod hp =>
      have hp0 : p ≠ 0 := by omega
      by_cases hrest : n / p ^ pe = 1
      · simp [onePrimeCell, decodePlaneCell, zeroBit, nonzeroBit,
          nonzeroProduct, oneBit, notOneBit, hp0, hrest]
      · simp [onePrimeCell, decodePlaneCell, zeroBit, nonzeroBit,
          nonzeroProduct, oneBit, notOneBit, hp0, hrest]
  | two prod p pe q qe hprod hp hq hpq =>
      have hp0 : p ≠ 0 := by omega
      have hq0 : q ≠ 0 := by omega
      have hrest : n / p ^ pe ≠ 1 := hpre.twoRest rfl
      have hpPow0 : p ^ pe ≠ 0 :=
        Nat.ne_of_gt (Nat.pow_pos (by omega))
      have hqPow0 : q ^ qe ≠ 0 :=
        Nat.ne_of_gt (Nat.pow_pos (by omega))
      have hpNorm : nonzeroProduct (p ^ pe) = p ^ pe := by
        unfold nonzeroProduct zeroBit
        rw [if_neg hpPow0]
        omega
      have hqNorm : nonzeroProduct (q ^ qe) = q ^ qe := by
        unfold nonzeroProduct zeroBit
        rw [if_neg hqPow0]
        omega
      have hqDvd : q ^ qe ∣ n / p ^ pe :=
        (Nat.dvd_div_iff_mul_dvd hdiv.pProdDvd).2 (by
          simpa only [twoPrimeCell, hpNorm, hqNorm] using hboth)
      have hcancel : q ^ qe * (n / p ^ pe / q ^ qe) = n / p ^ pe :=
        Nat.mul_div_cancel' hqDvd
      simpa [twoPrimeCell, decodePlaneCell, zeroBit, nonzeroBit,
        nonzeroProduct, oneBit, notOneBit, hp0, hq0, hrest] using hcancel

/-- Scratch-register interface between the shape-producing prefix and its two
exact-product guard blocks. -/
structure ClassGuardInputs (n : Nat) (x : PlaneCell) (out : AState) : Prop where
  pZero : out.regs 149 = zeroBit x.p
  pNonzero : out.regs 150 = nonzeroBit x.p
  pProd : out.regs 152 = nonzeroProduct x.pProd
  restOne : out.regs 157 = oneBit (decodePlaneCell n x).rest
  largeQ : out.regs 160 =
    notOneBit (decodePlaneCell n x).rest * zeroBit x.q
  markedQ : out.regs 162 =
    notOneBit (decodePlaneCell n x).rest * nonzeroBit x.q
  qProd : out.regs 165 = nonzeroProduct x.qProd
  candidate : out.regs 132 = n
  rest : out.regs rShapeRest = (decodePlaneCell n x).rest
  tail : out.regs rShapeTail = (decodePlaneCell n x).tail

/-- Besides the public six-register shape, the shape prefix retains the exact
selector and normalized-product inputs consumed by its two guard blocks. -/
theorem Cfg.classShapeBody_guardInputs
    (c : Cfg) (k : Nat) (s : AState) (n : Nat) (x : PlaneCell)
    (h132 : s.regs 132 = n)
    (h140 : s.regs 140 = x.prod) (h141 : s.regs 141 = x.p)
    (h142 : s.regs 142 = x.pe) (h143 : s.regs 143 = x.pProd)
    (h144 : s.regs 144 = x.q) (h145 : s.regs 145 = x.qe)
    (h146 : s.regs 146 = x.qProd)
    (hn : n < M) (hprod : x.prod < M)
    (hp : x.p < M) (hpe : x.pe < M)
    (hpp : nonzeroProduct x.pProd < M)
    (hq : x.q < M) (hqe : x.qe < M)
    (hqpp : nonzeroProduct x.qProd < M) :
    ClassGuardInputs n x (arun k s c.classShapeBody) := by
  let s0 := arun k s (lift Cfg.classNormalizeBody)
  let s1 := arun k s0 (lift Cfg.classFirstShapeBody)
  let s2 := arun k s1 (lift Cfg.classSecondFlagsBody)
  let s3 := arun k s2 (lift Cfg.classSecondShapeBody)
  let s4 := arun k s3 (lift Cfg.classTailBody)
  have hquot : n / nonzeroProduct x.pProd < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
  have hpProd0 : nonzeroProduct x.pProd ≠ 0 := by
    by_cases h : x.pProd = 0 <;>
      simp [nonzeroProduct, zeroBit, h]
  have hpProdLt : x.pProd < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_right x.pProd (zeroBit x.pProd)) hpp
  have hqProdLt : x.qProd < M :=
    Nat.lt_of_le_of_lt (Nat.le_add_right x.qProd (zeroBit x.qProd)) hqpp
  have hnorm := Cfg.classNormalizeBody_run k s
    (h140.symm ▸ hprod) (h143.symm ▸ hpProdLt)
  dsimp only at hnorm
  rcases hnorm with
    ⟨_, _, hs0pZero, hs0pNonzero, _, hs0pProd, hs0candidate, _⟩
  have hs0pZero' : s0.regs 149 = zeroBit x.p := by
    simpa only [s0, h141] using hs0pZero
  have hs0pNonzero' : s0.regs 150 = nonzeroBit x.p := by
    simpa only [s0, h141] using hs0pNonzero
  have hs0pProd' : s0.regs 152 = nonzeroProduct x.pProd := by
    simpa only [s0, h143] using hs0pProd
  have hs0candidate' : s0.regs 132 = n := by
    simpa only [s0, h132] using hs0candidate
  have hs0pLe : s0.regs 150 ≤ 1 := by
    rw [hs0pNonzero']
    simp [nonzeroBit, zeroBit]
  have hs0sel : s0.regs 150 + s0.regs 149 = 1 := by
    rw [hs0pNonzero', hs0pZero']
    by_cases hp0 : x.p = 0 <;> simp [nonzeroBit, zeroBit, hp0]
  have hs0pProd0 : s0.regs 152 ≠ 0 := hs0pProd'.symm ▸ hpProd0
  have hs0p : s0.regs 141 = x.p := by
    rw [arun_frame k 141 (lift Cfg.classNormalizeBody) (by rfl) s, h141]
  have hs0pe : s0.regs 142 = x.pe := by
    rw [arun_frame k 142 (lift Cfg.classNormalizeBody) (by rfl) s, h142]
  have hfirst := Cfg.classFirstShapeBody_run k s0 hs0pLe hs0sel
    hs0pProd0 (hs0candidate'.symm ▸ hn) (hs0p.symm ▸ hp) (hs0pe.symm ▸ hpe)
  dsimp only at hfirst
  rcases hfirst with
    ⟨_, _, _, _, hs1rest, _, _, _, _⟩
  have hs1rest' : s1.regs rShapeRest = (decodePlaneCell n x).rest := by
    rw [hs1rest, hs0pNonzero', hs0candidate', hs0pProd', hs0pZero']
    rfl
  have hs1q : s1.regs 144 = x.q := by
    rw [arun_frame k 144 (lift Cfg.classFirstShapeBody) (by rfl) s0,
      arun_frame k 144 (lift Cfg.classNormalizeBody) (by rfl) s, h144]
  have hflags := Cfg.classSecondFlagsBody_run k s1
  dsimp only at hflags
  rcases hflags with
    ⟨hs2restOne, _, _, hs2largeQ, _, hs2markedQ, _, _, _⟩
  have hs2rest : s2.regs rShapeRest = (decodePlaneCell n x).rest := by
    rw [arun_frame k rShapeRest (lift Cfg.classSecondFlagsBody) (by rfl) s1,
      hs1rest']
  have hs2q : s2.regs 144 = x.q := by
    rw [arun_frame k 144 (lift Cfg.classSecondFlagsBody) (by rfl) s1,
      hs1q]
  have hs2restOne' :
      s2.regs 157 = oneBit (decodePlaneCell n x).rest := by
    rw [hs2restOne, hs1rest']
  have hs2largeQ' : s2.regs 160 =
      notOneBit (decodePlaneCell n x).rest * zeroBit x.q := by
    rw [hs2largeQ, hs1rest', hs1q]
  have hs2markedQ' : s2.regs 162 =
      notOneBit (decodePlaneCell n x).rest * nonzeroBit x.q := by
    rw [hs2markedQ, hs1rest', hs1q]
  have hs3markedQ : s3.regs 162 = s2.regs 162 :=
    arun_frame k 162 (lift Cfg.classSecondShapeBody) (by rfl) s2
  have hs3rest : s3.regs rShapeRest = (decodePlaneCell n x).rest := by
    rw [arun_frame k rShapeRest (lift Cfg.classSecondShapeBody) (by rfl) s2,
      hs2rest]
  have hs3qProd : s3.regs 146 = x.qProd := by
    rw [arun_frame k 146 (lift Cfg.classSecondShapeBody) (by rfl) s2,
      arun_frame k 146 (lift Cfg.classSecondFlagsBody) (by rfl) s1,
      arun_frame k 146 (lift Cfg.classFirstShapeBody) (by rfl) s0,
      arun_frame k 146 (lift Cfg.classNormalizeBody) (by rfl) s, h146]
  have hs2markedLe : s2.regs 162 ≤ 1 := by
    rw [hs2markedQ']
    by_cases hr : (decodePlaneCell n x).rest = 1 <;>
      by_cases hq0 : x.q = 0 <;>
        simp [notOneBit, oneBit, nonzeroBit, zeroBit, hr, hq0]
  have hs3markedLe : s3.regs 162 ≤ 1 := hs3markedQ ▸ hs2markedLe
  have hrestLt : (decodePlaneCell n x).rest < M := by
    by_cases hp0 : x.p = 0
    · simp [decodePlaneCell, nonzeroBit, zeroBit, hp0, M]
    · simpa [decodePlaneCell, nonzeroBit, zeroBit, hp0] using hquot
  have htail := Cfg.classTailBody_run k s3 hs3markedLe
    (hs3qProd.symm ▸ hqProdLt) (hs3rest.symm ▸ hrestLt)
  dsimp only at htail
  rcases htail with ⟨_, hs4qProd, _, _, _, hs4rest, _⟩
  have hs4qProd' : s4.regs 165 = nonzeroProduct x.qProd := by
    rw [hs4qProd, hs3qProd]
  have hout : arun k s c.classShapeBody = s4 := by
    simp only [Cfg.classShapeBody, LeanCompCert.Verified.ArrayScalarBlock.lift_append,
      LeanCompCert.Verified.ArrayFoldBridge.arun_append]
    rfl
  have hs4pZero : s4.regs 149 = s0.regs 149 := by
    simpa only [LeanCompCert.Verified.ArrayScalarBlock.lift_append,
      LeanCompCert.Verified.ArrayFoldBridge.arun_append] using
      (arun_frame k 149
        (lift (Cfg.classFirstShapeBody ++ Cfg.classSecondFlagsBody ++
          Cfg.classSecondShapeBody ++ Cfg.classTailBody)) (by rfl) s0)
  have hs4pNonzero : s4.regs 150 = s0.regs 150 := by
    simpa only [LeanCompCert.Verified.ArrayScalarBlock.lift_append,
      LeanCompCert.Verified.ArrayFoldBridge.arun_append] using
      (arun_frame k 150
        (lift (Cfg.classFirstShapeBody ++ Cfg.classSecondFlagsBody ++
          Cfg.classSecondShapeBody ++ Cfg.classTailBody)) (by rfl) s0)
  have hs4pProd : s4.regs 152 = s0.regs 152 := by
    simpa only [LeanCompCert.Verified.ArrayScalarBlock.lift_append,
      LeanCompCert.Verified.ArrayFoldBridge.arun_append] using
      (arun_frame k 152
        (lift (Cfg.classFirstShapeBody ++ Cfg.classSecondFlagsBody ++
          Cfg.classSecondShapeBody ++ Cfg.classTailBody)) (by rfl) s0)
  have hs4restOne : s4.regs 157 = s2.regs 157 := by
    simpa only [LeanCompCert.Verified.ArrayScalarBlock.lift_append,
      LeanCompCert.Verified.ArrayFoldBridge.arun_append] using
      (arun_frame k 157
        (lift (Cfg.classSecondShapeBody ++ Cfg.classTailBody)) (by rfl) s2)
  have hs4largeQ : s4.regs 160 = s2.regs 160 := by
    simpa only [LeanCompCert.Verified.ArrayScalarBlock.lift_append,
      LeanCompCert.Verified.ArrayFoldBridge.arun_append] using
      (arun_frame k 160
        (lift (Cfg.classSecondShapeBody ++ Cfg.classTailBody)) (by rfl) s2)
  have hs4markedQ : s4.regs 162 = s2.regs 162 := by
    rw [arun_frame k 162 (lift Cfg.classTailBody) (by rfl) s3,
      hs3markedQ]
  have hshape := c.classShapeBody_run k s n x h132 h140 h141 h142 h143
    h144 h145 h146 hn hp hpe hpp hq hqe hqpp
  have hfinalRest :
      (arun k s c.classShapeBody).regs rShapeRest =
        (decodePlaneCell n x).rest := by
    have := congrArg Shape.rest hshape
    simpa [shapeRegs] using this
  have hfinalTail :
      (arun k s c.classShapeBody).regs rShapeTail =
        (decodePlaneCell n x).tail := by
    have := congrArg Shape.tail hshape
    simpa [shapeRegs] using this
  refine {
    pZero := hout.symm ▸ hs4pZero.trans hs0pZero'
    pNonzero := hout.symm ▸ hs4pNonzero.trans hs0pNonzero'
    pProd := hout.symm ▸ hs4pProd.trans hs0pProd'
    restOne := hout.symm ▸ hs4restOne.trans hs2restOne'
    largeQ := hout.symm ▸ hs4largeQ.trans hs2largeQ'
    markedQ := hout.symm ▸ hs4markedQ.trans hs2markedQ'
    qProd := hout.symm ▸ hs4qProd'
    candidate := by
      rw [arun_frame k 132 c.classShapeBody (by rfl) s, h132]
    rest := hfinalRest
    tail := hfinalTail }

/-- Observable counter effect of a successful exact-product guard suffix. -/
structure ClassGuardResult (before out : AState) : Prop where
  viol : out.regs rViol = before.regs rViol
  vshape : out.regs rVShape = before.regs rVShape
  seen : out.regs rSeen = before.regs rSeen + 1
  array : out.arr = before.arr

/-- On a source-related cell satisfying the finite row-fold invariants, both
physical exact-product guards return one.  The emitted commit therefore
advances `seen` but adds zero to both violation counters. -/
theorem Cfg.classGuardBody_correct
    (c : Cfg) (k : Nat) (s : AState) (n : Nat)
    (x : PlaneCell) (cell : Cell)
    (hinputs : ClassGuardInputs n x s)
    (hrel : CellRel x cell)
    (hdiv : CellDivisorBounds n cell)
    (hshape : CellFactorShape cell)
    (hpre : CellClassifyPre n cell)
    (hn : n < M) (hpp : nonzeroProduct x.pProd < M)
    (hqpp : nonzeroProduct x.qProd < M)
    (hphase : s.regs 11 = 1)
    (hviol : s.regs rViol < M)
    (hvshape : s.regs rVShape < M)
    (hseen : s.regs rSeen + 1 < M) :
    ClassGuardResult s (arun k s c.classGuardBody) := by
  let g1 := arun k s (lift Cfg.classFirstGuardBody)
  let g2 := arun k g1 (lift Cfg.classSecondGuardBody)
  let g3 := arun k g2 (lift Cfg.classGuardCommitBody)
  rcases hinputs with
    ⟨hpZero, hpNonzero, hpProd, hrestOne, hlargeQ, hmarkedQ,
      hqProd, hcandidate, hrest, htail⟩
  have hfirstExact := hrel.decodePlaneCell_firstGuard_exact n hdiv hpre
  have hpLe : s.regs 150 ≤ 1 := by
    rw [hpNonzero]
    simp [nonzeroBit, zeroBit]
  have hpSel : s.regs 150 + s.regs 149 = 1 := by
    rw [hpNonzero, hpZero]
    by_cases hp0 : x.p = 0 <;> simp [nonzeroBit, zeroBit, hp0]
  have hfirstProd :
      (s.regs 149 * s.regs 132 + s.regs 150 * s.regs 152) *
          s.regs rShapeRest < M := by
    rw [hpZero, hpNonzero, hpProd, hcandidate, hrest, hfirstExact]
    exact hn
  have hfirstRun := Cfg.classFirstGuardBody_run k s hpLe hpSel
    (hcandidate.symm ▸ hn) (hpProd.symm ▸ hpp) hfirstProd
  dsimp only at hfirstRun
  rcases hfirstRun with ⟨_, _, hg1first, _, _, hg1array⟩
  have hg1first' : g1.regs 169 = 1 := by
    rw [hg1first, hpZero, hpNonzero, hpProd, hcandidate, hrest,
      hfirstExact]
    simp
  have hg1rest : g1.regs rShapeRest = (decodePlaneCell n x).rest := by
    rw [arun_frame k rShapeRest (lift Cfg.classFirstGuardBody) (by rfl) s,
      hrest]
  have hg1tail : g1.regs rShapeTail = (decodePlaneCell n x).tail := by
    rw [arun_frame k rShapeTail (lift Cfg.classFirstGuardBody) (by rfl) s,
      htail]
  have hg1restOne : g1.regs 157 = oneBit (decodePlaneCell n x).rest := by
    rw [arun_frame k 157 (lift Cfg.classFirstGuardBody) (by rfl) s,
      hrestOne]
  have hg1largeQ : g1.regs 160 =
      notOneBit (decodePlaneCell n x).rest * zeroBit x.q := by
    rw [arun_frame k 160 (lift Cfg.classFirstGuardBody) (by rfl) s,
      hlargeQ]
  have hg1markedQ : g1.regs 162 =
      notOneBit (decodePlaneCell n x).rest * nonzeroBit x.q := by
    rw [arun_frame k 162 (lift Cfg.classFirstGuardBody) (by rfl) s,
      hmarkedQ]
  have hg1qProd : g1.regs 165 = nonzeroProduct x.qProd := by
    rw [arun_frame k 165 (lift Cfg.classFirstGuardBody) (by rfl) s,
      hqProd]
  have hlargeLe : g1.regs 160 ≤ 1 := by
    rw [hg1largeQ]
    by_cases hr : (decodePlaneCell n x).rest = 1 <;>
      by_cases hq0 : x.q = 0 <;>
        simp [notOneBit, oneBit, zeroBit, hr, hq0]
  have hmarkedLe : g1.regs 162 ≤ 1 := by
    rw [hg1markedQ]
    by_cases hr : (decodePlaneCell n x).rest = 1 <;>
      by_cases hq0 : x.q = 0 <;>
        simp [notOneBit, oneBit, nonzeroBit, zeroBit, hr, hq0]
  have honeLe : g1.regs 157 ≤ 1 := by
    rw [hg1restOne]
    by_cases hr : (decodePlaneCell n x).rest = 1 <;>
      simp [oneBit, hr]
  have hsecondSel :
      g1.regs 160 + g1.regs 162 + g1.regs 157 = 1 := by
    rw [hg1largeQ, hg1markedQ, hg1restOne]
    by_cases hr : (decodePlaneCell n x).rest = 1 <;>
      by_cases hq0 : x.q = 0 <;>
        simp [notOneBit, oneBit, nonzeroBit, zeroBit, hr, hq0]
  have hrestLt : (decodePlaneCell n x).rest < M := by
    by_cases hp0 : x.p = 0
    · simp [decodePlaneCell, nonzeroBit, zeroBit, hp0, M]
    · have hquot : n / nonzeroProduct x.pProd < M :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn
      simpa [decodePlaneCell, nonzeroBit, zeroBit, hp0] using hquot
  have htailFormula : (decodePlaneCell n x).tail =
      (notOneBit (decodePlaneCell n x).rest * nonzeroBit x.q) *
          ((decodePlaneCell n x).rest / nonzeroProduct x.qProd) +
        (1 - notOneBit (decodePlaneCell n x).rest * nonzeroBit x.q) := by
    rfl
  have htailLt : (decodePlaneCell n x).tail < M := by
    rw [htailFormula]
    by_cases hr : (decodePlaneCell n x).rest = 1
    · simp [notOneBit, oneBit, hr, M]
    · by_cases hq0 : x.q = 0
      · simp [nonzeroBit, zeroBit, hq0, M]
      · have hquot :
          (decodePlaneCell n x).rest / nonzeroProduct x.qProd < M :=
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hrestLt
        simpa [notOneBit, oneBit, nonzeroBit, zeroBit, hr, hq0] using hquot
  have hsecondExact :=
    hrel.decodePlaneCell_secondGuard_exact n hdiv hshape hpre
  have hsecondProd :
      (g1.regs 160 * g1.regs rShapeRest + g1.regs 162 * g1.regs 165 +
          g1.regs 157) * g1.regs rShapeTail < M := by
    rw [hg1largeQ, hg1rest, hg1markedQ, hg1qProd, hg1restOne,
      hg1tail, hsecondExact]
    exact hrestLt
  have hsecondRun := Cfg.classSecondGuardBody_run k g1 hlargeLe
    hmarkedLe honeLe hsecondSel (hg1rest.symm ▸ hrestLt)
    (hg1qProd.symm ▸ hqpp) (hg1tail.symm ▸ htailLt) hsecondProd
  dsimp only at hsecondRun
  rcases hsecondRun with ⟨_, _, hg2second, _, _, hg2array⟩
  have hg2second' : g2.regs 171 = 1 := by
    rw [hg2second, hg1largeQ, hg1rest, hg1markedQ, hg1qProd,
      hg1restOne, hg1tail, hsecondExact]
    simp
  have hg2first : g2.regs 169 = 1 := by
    rw [arun_frame k 169 (lift Cfg.classSecondGuardBody) (by rfl) g1,
      hg1first']
  have hg2phase : g2.regs 11 = 1 := by
    rw [arun_frame k 11 (lift Cfg.classSecondGuardBody) (by rfl) g1,
      arun_frame k 11 (lift Cfg.classFirstGuardBody) (by rfl) s, hphase]
  have hg2viol : g2.regs rViol = s.regs rViol := by
    rw [arun_frame k rViol (lift Cfg.classSecondGuardBody) (by rfl) g1,
      arun_frame k rViol (lift Cfg.classFirstGuardBody) (by rfl) s]
  have hg2vshape : g2.regs rVShape = s.regs rVShape := by
    rw [arun_frame k rVShape (lift Cfg.classSecondGuardBody) (by rfl) g1,
      arun_frame k rVShape (lift Cfg.classFirstGuardBody) (by rfl) s]
  have hg2seen : g2.regs rSeen = s.regs rSeen := by
    rw [arun_frame k rSeen (lift Cfg.classSecondGuardBody) (by rfl) g1,
      arun_frame k rSeen (lift Cfg.classFirstGuardBody) (by rfl) s]
  have hcommit := Cfg.classGuardCommitBody_run k g2
    (by rw [hg2first]; omega) (by rw [hg2second']; omega) hg2phase
    (by rw [hg2first, hg2second', hg2viol]; simpa using hviol)
    (by rw [hg2first, hg2second', hg2vshape]; simpa using hvshape)
    (hg2seen.symm ▸ hseen)
  dsimp only at hcommit
  rcases hcommit with ⟨_, _, _, hg3viol, hg3vshape, hg3seen, hg3array⟩
  have hout : arun k s c.classGuardBody = g3 := by
    simp only [Cfg.classGuardBody,
      LeanCompCert.Verified.ArrayScalarBlock.lift_append,
      LeanCompCert.Verified.ArrayFoldBridge.arun_append]
    rfl
  refine {
    viol := by rw [hout, hg3viol, hg2first, hg2second', hg2viol]; simp
    vshape := by rw [hout, hg3vshape, hg2first, hg2second', hg2vshape]; simp
    seen := by rw [hout, hg3seen, hg2seen]
    array := by
      rw [hout, hg3array, hg2array, hg1array] }

/-- Counter and array effect of the complete scalar decode/guard block. -/
structure ClassDecodeResult (before out : AState) : Prop where
  viol : out.regs rViol = before.regs rViol
  vshape : out.regs rVShape = before.regs rVShape
  seen : out.regs rSeen = before.regs rSeen + 1
  array : out.arr = before.arr

/-- The complete emitted scalar classifier decode succeeds on a related
finite row-fold cell.  This composes the shape prefix with the verified guard
suffix without normalizing the combined instruction list. -/
theorem Cfg.classDecodeBody_correct
    (c : Cfg) (k : Nat) (s : AState) (n : Nat)
    (x : PlaneCell) (cell : Cell)
    (hrel : CellRel x cell)
    (hdiv : CellDivisorBounds n cell)
    (hshape : CellFactorShape cell)
    (hpre : CellClassifyPre n cell)
    (h132 : s.regs 132 = n)
    (h140 : s.regs 140 = x.prod) (h141 : s.regs 141 = x.p)
    (h142 : s.regs 142 = x.pe) (h143 : s.regs 143 = x.pProd)
    (h144 : s.regs 144 = x.q) (h145 : s.regs 145 = x.qe)
    (h146 : s.regs 146 = x.qProd)
    (hn : n < M) (hprod : x.prod < M)
    (hp : x.p < M) (hpe : x.pe < M)
    (hpp : nonzeroProduct x.pProd < M)
    (hq : x.q < M) (hqe : x.qe < M)
    (hqpp : nonzeroProduct x.qProd < M)
    (hphase : s.regs 11 = 1)
    (hviol : s.regs rViol < M)
    (hvshape : s.regs rVShape < M)
    (hseen : s.regs rSeen + 1 < M) :
    ClassDecodeResult s (arun k s (lift Cfg.classDecodeBody)) := by
  let shaped := arun k s c.classShapeBody
  let guarded := arun k shaped c.classGuardBody
  have hinputs := c.classShapeBody_guardInputs k s n x h132 h140 h141
    h142 h143 h144 h145 h146 hn hprod hp hpe hpp hq hqe hqpp
  have hshapedPhase : shaped.regs 11 = 1 := by
    rw [arun_frame k 11 c.classShapeBody (by rfl) s, hphase]
  have hshapedViol : shaped.regs rViol = s.regs rViol :=
    arun_frame k rViol c.classShapeBody (by rfl) s
  have hshapedVShape : shaped.regs rVShape = s.regs rVShape :=
    arun_frame k rVShape c.classShapeBody (by rfl) s
  have hshapedSeen : shaped.regs rSeen = s.regs rSeen :=
    arun_frame k rSeen c.classShapeBody (by rfl) s
  have hguard := c.classGuardBody_correct k shaped n x cell hinputs hrel
    hdiv hshape hpre hn hpp hqpp hshapedPhase
    (hshapedViol.symm ▸ hviol) (hshapedVShape.symm ▸ hvshape)
    (hshapedSeen.symm ▸ hseen)
  have hshapedArray : shaped.arr = s.arr :=
    LeanCompCert.Ports.ArraySegMobiusSignal.arun_arr_frame
      k c.classShapeBody s (by rfl)
  have hout : arun k s (lift Cfg.classDecodeBody) = guarded := by
    rw [c.classDecodeBody_split,
      LeanCompCert.Verified.ArrayFoldBridge.arun_append]
  refine {
    viol := by rw [hout, hguard.viol, hshapedViol]
    vshape := by rw [hout, hguard.vshape, hshapedVShape]
    seen := by rw [hout, hguard.seen, hshapedSeen]
    array := by rw [hout, hguard.array, hshapedArray] }

end LeanCompCert.Ports.RamareCombined100M.ShapeSieve

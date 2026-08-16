import LeanCompCert.Ports.A7BoundaryProgram
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Source semantics of the emitted A.7 transcript checker

This module is intentionally staged.  It first connects the literal row
loads to the already-proved four-word comparison, without unfolding the
remainder of the row checker.  Later stages compose the Boolean guards and
the finite edge cursor.
-/

namespace LeanCompCert.Ports.A7BoundaryProgram

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.A7BoundaryRow

def EncodedRow.Words (r : EncodedRow) : Prop :=
  r.edge < M ∧ r.depth < M ∧ r.index < M ∧
    r.norm0 < M ∧ r.norm1 < M ∧ r.norm2 < M ∧
    r.normShift < M ∧
    r.zeta0 < M ∧ r.zeta1 < M ∧ r.zeta2 < M ∧
    r.zetaShift < M ∧ r.startGrid < M ∧ r.finishGrid < M ∧
    2 ^ r.depth < M

theorem limbs4_words (n : Nat) : (limbs4 n).WF := by
  constructor
  · exact Nat.mod_lt _ (by decide)
  constructor
  · exact Nat.mod_lt _ (by decide)
  constructor <;> exact Nat.mod_lt _ (by decide)

/-- The eight literal moves install precisely the two values compared by the
wide block.  This theorem is independent of transcript size. -/
theorem comparePrelude_run (r : EncodedRow) (k : Nat) (s : AState)
    (hw : r.Words) :
    let out := arun k s (comparePrelude r)
    out.regs rX0 = r.norm0 ∧
      out.regs rX1 = r.norm1 ∧
      out.regs rX2 = r.norm2 ∧
      out.regs 11 = 0 ∧
      out.regs rY0 = r.limit.l0 ∧
      out.regs rY1 = r.limit.l1 ∧
      out.regs rY2 = r.limit.l2 ∧
      out.regs rY3 = r.limit.l3 := by
  rcases hw with
    ⟨_, _, _, hn0, hn1, hn2, _, _, _, _, _, _, _, _⟩
  have hlim := limbs4_words (targetLimit r.normShift)
  rcases hlim with ⟨hl0, hl1, hl2, hl3⟩
  simp [comparePrelude, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, rX0, rX1, rX2, rY0, rY1, rY2, rY3,
    rBorrow, rLt, rEq, rEqBorrow, EncodedRow.limit,
    Nat.mod_eq_of_lt hn0, Nat.mod_eq_of_lt hn1, Nat.mod_eq_of_lt hn2,
    Nat.mod_eq_of_lt hl0, Nat.mod_eq_of_lt hl1,
    Nat.mod_eq_of_lt hl2, Nat.mod_eq_of_lt hl3]

/-- The actual literal prelude followed by the actual comparison instructions
returns one exactly when the retained 192-bit mantissa lies below its
four-word threshold. -/
theorem compareStage_run_eq_one_iff (r : EncodedRow) (k : Nat) (s : AState)
    (hw : r.Words) :
    (arun k (arun k s (comparePrelude r)) compareBody).regs rBorrow = 1 ↔
      r.norm.val < r.limit.val := by
  let loaded := arun k s (comparePrelude r)
  have hp := comparePrelude_run r k s hw
  dsimp only at hp
  have hlim : r.limit.WF := by
    simpa [EncodedRow.limit, B] using
      (limbs4_words (targetLimit r.normShift))
  have hcmp := compareBody_run_eq_one_iff k loaded
    (by simpa [loaded, hp.1] using hw.2.2.2.1)
    (by simpa [loaded, hp.2.1] using hw.2.2.2.2.1)
    (by simpa [loaded, hp.2.2.1] using hw.2.2.2.2.2.1)
    (by simpa [loaded, hp.2.2.2.2.1] using hlim.1)
    (by simpa [loaded, hp.2.2.2.2.2.1] using hlim.2.1)
    (by simpa [loaded, hp.2.2.2.2.2.2.1] using hlim.2.2.1)
    (by simpa [loaded, hp.2.2.2.2.2.2.2] using hlim.2.2.2)
    (by simpa [loaded] using hp.2.2.2.1)
  rw [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.2.1,
    hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2] at hcmp
  simpa [loaded, EncodedRow.norm, EncodedRow.limit] using hcmp

theorem compareStage_run_le_one (r : EncodedRow) (k : Nat) (s : AState)
    (hw : r.Words) :
    (arun k (arun k s (comparePrelude r)) compareBody).regs rBorrow ≤ 1 := by
  let loaded := arun k s (comparePrelude r)
  have hp := comparePrelude_run r k s hw
  dsimp only at hp
  have hlim : r.limit.WF := by
    simpa [EncodedRow.limit, B] using
      (limbs4_words (targetLimit r.normShift))
  have hrun := compareBody_run k loaded
    (by simpa [loaded, hp.1] using hw.2.2.2.1)
    (by simpa [loaded, hp.2.1] using hw.2.2.2.2.1)
    (by simpa [loaded, hp.2.2.1] using hw.2.2.2.2.2.1)
    (by simpa [loaded, hp.2.2.2.2.1] using hlim.1)
    (by simpa [loaded, hp.2.2.2.2.2.1] using hlim.2.1)
    (by simpa [loaded, hp.2.2.2.2.2.2.1] using hlim.2.2.1)
    (by simpa [loaded, hp.2.2.2.2.2.2.2] using hlim.2.2.2)
    (by simpa [loaded] using hp.2.2.2.1)
  rw [hrun]
  exact borrow4_le_one _ _

theorem compareStage_frame (r : EncodedRow) (k : Nat) (s : AState) :
    let out := arun k (arun k s (comparePrelude r)) compareBody
    out.regs rCurrentEdge = s.regs rCurrentEdge ∧
      out.regs rCursor = s.regs rCursor ∧
      out.regs rViol = s.regs rViol := by
  simp [comparePrelude, compareBody, borrowLimbBody, arun, astep,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp,
    rX0, rX1, rX2, rY0, rY1, rY2, rY3,
    rBorrow, rLt, rEq, rEqBorrow,
    rCurrentEdge, rCursor, rViol]

def bit (p : Prop) [Decidable p] : Nat := if p then 1 else 0

/-- Transparent zero/one model of every guard after the wide comparison. -/
def rowBit (r : EncodedRow) (currentEdge cursor compare : Nat) : Nat :=
  let ok0 := compare
  let ok1 := ok0 * bit (r.edge < 4)
  let ok2 := ok1 * bit (r.depth ≤ gridDepth)
  let ok3 := ok2 * bit (r.index < 2 ^ r.depth)
  let ok4 := ok3 * bit (r.norm0 ≠ 0 ∨ r.norm1 ≠ 0 ∨ r.norm2 ≠ 0)
  let ok5 := ok4 * bit (178 ≤ r.normShift)
  let ok6 := ok5 * bit (r.normShift ≤ 196)
  let ok7 := ok6 * bit (r.zeta0 ≠ 0 ∨ r.zeta1 ≠ 0 ∨ r.zeta2 ≠ 0)
  let ok8 := ok7 * bit (182 ≤ r.zetaShift)
  let ok9 := ok8 * bit (r.zetaShift ≤ 198)
  let ok10 := ok9 * bit (r.startGrid < r.finishGrid)
  let ok11 := ok10 * bit (r.finishGrid ≤ gridScale)
  ok11 * bit
    ((r.edge = currentEdge ∧ r.startGrid = cursor) ∨
      (r.edge = currentEdge + 1 ∧ cursor = gridScale ∧ r.startGrid = 0))

theorem bit_le_one (p : Prop) [Decidable p] : bit p ≤ 1 := by
  unfold bit
  split <;> omega

private theorem mul_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    a * b ≤ 1 := by
  simpa using Nat.mul_le_mul ha hb

@[simp] private theorem flag_mul (p q : Prop) [Decidable p] [Decidable q] :
    (if p then 1 else 0) * (if q then 1 else 0) =
      if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

@[simp] private theorem flag_mul_mod (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0) * (if q then 1 else 0)) % M =
      if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, M]

@[simp] private theorem flag_bor_mod (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0) ||| (if q then 1 else 0)) % M =
      if p ∨ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, M]

@[simp] private theorem flag_mod_bor_mod
    (p q : Prop) [Decidable p] [Decidable q] :
    (((if p then 1 else 0) % M ||| (if q then 1 else 0) % M) % M) =
      if p ∨ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, M]

@[simp] private theorem flag_sub (p : Prop) [Decidable p] :
    (1 + (M - (if p then 1 else 0))) % M =
      if p then 0 else 1 := by
  by_cases hp : p <;> simp [hp, M]

private theorem finish_flag (p : Prop) [Decidable p] (viol : Nat)
    (hViol : viol < M) (hViolSucc : viol + 1 < M) :
    ((if p then 1 else 0) % M = (if p then 1 else 0)) ∧
      (viol + (1 + (M - (if p then 1 else 0) % M))) % M =
        viol + (1 - (if p then 1 else 0)) := by
  by_cases hp : p
  · simp only [if_pos hp, Nat.sub_self, Nat.add_zero]
    constructor
    · exact Nat.mod_eq_of_lt (by decide)
    · rw [show 1 + (M - 1 % M) = M by decide]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hViol]
  · simp only [if_neg hp, Nat.zero_mod, Nat.sub_zero]
    constructor
    · trivial
    · rw [show viol + (1 + M) = (viol + 1) + M by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hViolSucc]

@[simp] private theorem nonzero3_machine (a b c : Nat) :
    ((((if a = 0 then 0 else 1) ||| (if b = 0 then 0 else 1)) % M |||
        (if c = 0 then 0 else 1)) % M) =
      if a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 then 1 else 0 := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    by_cases hc : c = 0 <;> simp [ha, hb, hc, M]

@[simp] private theorem nonzero3_imp_iff (a b c : Nat) :
    (a = 0 → b = 0 → c ≠ 0) ↔ (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    by_cases hc : c = 0 <;> simp [ha, hb, hc]

@[simp] private theorem topology_machine
    (p q r t u : Prop) [Decidable p] [Decidable q] [Decidable r]
    [Decidable t] [Decidable u] :
    ((((if p then 1 else 0) * (if q then 1 else 0)) % M |||
        (((if r then 1 else 0) * (if t then 1 else 0)) *
          (if u then 1 else 0)) % M) % M) =
      if (p ∧ q) ∨ (r ∧ t ∧ u) then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
    by_cases ht : t <;> by_cases hu : u <;> simp [hp, hq, hr, ht, hu, M]

theorem rowBit_le_one (r : EncodedRow) (currentEdge cursor compare : Nat)
    (hcompare : compare ≤ 1) : rowBit r currentEdge cursor compare ≤ 1 := by
  unfold rowBit
  apply mul_le_one <;> try apply mul_le_one <;>
    try apply mul_le_one <;> try apply mul_le_one <;>
    try apply mul_le_one <;> try apply mul_le_one <;>
    try apply mul_le_one <;> try apply mul_le_one <;>
    try apply mul_le_one <;> try apply mul_le_one <;>
    try apply mul_le_one <;> try apply mul_le_one
  all_goals first | exact hcompare | exact bit_le_one _

private theorem limbs3_pos_iff (a b c : Nat) :
    0 < a + B * (b + B * (c + B * 0)) ↔
      a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by
  simp only [Nat.mul_zero, Nat.add_zero]
  constructor
  · intro h
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · right; right
        intro hc
        subst a; subst b; subst c
        omega
      · exact Or.inr (Or.inl hb)
    · exact Or.inl ha
  · intro h
    have hB : 0 < B := by decide
    rcases h with ha | hb | hc
    · have : 0 < a := Nat.pos_of_ne_zero ha
      exact Nat.add_pos_left this _
    · have : 0 < b := Nat.pos_of_ne_zero hb
      exact Nat.add_pos_right _ (Nat.mul_pos hB (Nat.add_pos_left this _))
    · have : 0 < c := Nat.pos_of_ne_zero hc
      exact Nat.add_pos_right _ (Nat.mul_pos hB
        (Nat.add_pos_right _ (Nat.mul_pos hB this)))

theorem norm_pos_iff (r : EncodedRow) :
    0 < r.norm.val ↔ r.norm0 ≠ 0 ∨ r.norm1 ≠ 0 ∨ r.norm2 ≠ 0 := by
  simpa [EncodedRow.norm, Limbs4.val] using
    (limbs3_pos_iff r.norm0 r.norm1 r.norm2)

theorem zeta_pos_iff (r : EncodedRow) :
    0 < r.zeta.val ↔ r.zeta0 ≠ 0 ∨ r.zeta1 ≠ 0 ∨ r.zeta2 ≠ 0 := by
  simpa [EncodedRow.zeta, Limbs4.val] using
    (limbs3_pos_iff r.zeta0 r.zeta1 r.zeta2)

/-- The transparent zero/one guard is one exactly for the source-shaped row
predicate, once the wide comparison result is given its proved meaning. -/
theorem rowBit_eq_one_iff (r : EncodedRow)
    (currentEdge cursor compare : Nat) (hCompareLe : compare ≤ 1)
    (hCompare : compare = 1 ↔ r.norm.val < r.limit.val) :
    rowBit r currentEdge cursor compare = 1 ↔
      r.ValidAfter currentEdge cursor := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hCompareLe with rfl | rfl
  · have hnot : ¬r.norm.val < r.limit.val := by
      intro hlt
      have := hCompare.mpr hlt
      omega
    simp [rowBit, EncodedRow.ValidAfter, bit, hnot]
  · have hlt : r.norm.val < r.limit.val := hCompare.mp rfl
    by_cases hsame : r.edge = currentEdge ∧ r.startGrid = cursor
    · simp [rowBit, EncodedRow.ValidAfter, bit, hlt, hsame,
        norm_pos_iff, zeta_pos_iff, and_assoc]
    · by_cases hnext :
          r.edge = currentEdge + 1 ∧ cursor = gridScale ∧ r.startGrid = 0
      · simp [rowBit, EncodedRow.ValidAfter, bit, hlt, hsame, hnext,
          norm_pos_iff, zeta_pos_iff, and_assoc]
      · simp [rowBit, EncodedRow.ValidAfter, bit, hlt, hsame, hnext,
          norm_pos_iff, zeta_pos_iff, and_assoc]

def failureBit (r : EncodedRow) (currentEdge cursor : Nat) : Nat :=
  if r.ValidAfter currentEdge cursor then 0 else 1

theorem one_sub_rowBit (r : EncodedRow)
    (currentEdge cursor compare : Nat) (hCompareLe : compare ≤ 1)
    (hCompare : compare = 1 ↔ r.norm.val < r.limit.val) :
    1 - rowBit r currentEdge cursor compare =
      failureBit r currentEdge cursor := by
  have hiff := rowBit_eq_one_iff r currentEdge cursor compare
    hCompareLe hCompare
  have hle := rowBit_le_one r currentEdge cursor compare hCompareLe
  by_cases hvalid : r.ValidAfter currentEdge cursor
  · have hone := hiff.mpr hvalid
    simp [failureBit, hvalid, hone]
  · have hne : rowBit r currentEdge cursor compare ≠ 1 := by
      intro hone
      exact hvalid (hiff.mp hone)
    have hzero : rowBit r currentEdge cursor compare = 0 := by omega
    simp [failureBit, hvalid, hzero]

set_option maxRecDepth 100000

/-- Exact scalar result of the non-wide row guard.  The theorem deliberately
keeps the comparison result abstract; `compareStage_run_eq_one_iff` supplies
its source meaning at the composition boundary. -/
theorem guardBody_run (r : EncodedRow) (k currentEdge cursor compare viol : Nat)
    (s : AState)
    (hEdge : s.regs rCurrentEdge = currentEdge)
    (hCursor : s.regs rCursor = cursor)
    (hCompare : s.regs rBorrow = compare)
    (hViol : s.regs rViol = viol)
    (hWords : r.Words)
    (hEdgeM : currentEdge < M) (hEdgeSuccM : currentEdge + 1 < M)
    (hCursorM : cursor < M)
    (hCompareLe : compare ≤ 1) (hViolM : viol + 1 < M) :
    let out := arun k s (guardBody r)
    out.regs rOK = rowBit r currentEdge cursor compare ∧
      out.regs rViol = viol + (1 - rowBit r currentEdge cursor compare) ∧
      out.regs rCurrentEdge = r.edge ∧
      out.regs rCursor = r.finishGrid := by
  rcases hWords with
    ⟨hREdgeM, hDepthM, hIndexM, hn0, hn1, hn2, hNSM,
      hz0, hz1, hz2, hZSM, hStartM, hFinishM, hPowM⟩
  have hCompareM : compare < M := by omega
  have hBit := rowBit_le_one r currentEdge cursor compare hCompareLe
  have hBadM : 1 - rowBit r currentEdge cursor compare < M := by omega
  have hNewM : viol + (1 - rowBit r currentEdge cursor compare) < M := by omega
  have hViolOnlyM : viol < M := by omega
  have h4M : 4 % M = 4 := by decide
  have h17M : 17 % M = 17 := by decide
  have h178M : 178 % M = 178 := by decide
  have h182M : 182 % M = 182 := by decide
  have h196M : 196 % M = 196 := by decide
  have h198M : 198 % M = 198 := by decide
  have hGridM : gridScale % M = gridScale := by decide
  have h131072M : 131072 % M = 131072 := by decide
  have hEdge' : s.regs 12 = currentEdge := by
    simpa [rCurrentEdge] using hEdge
  have hCursor' : s.regs 13 = cursor := by
    simpa [rCursor] using hCursor
  have hCompare' : s.regs 7 = compare := by
    simpa [rBorrow] using hCompare
  have hViol' : s.regs 14 = viol := by
    simpa [rViol] using hViol
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hCompareLe with rfl | rfl
  all_goals
  simp [guardBody, gate, arun, astep, AState.writeReg, sdest, sval,
    denoteOperand, denoteOp, rowBit, bit, hEdge', hCursor', hCompare', hViol',
    Nat.mod_eq_of_lt hREdgeM, Nat.mod_eq_of_lt hDepthM,
    Nat.mod_eq_of_lt hIndexM, Nat.mod_eq_of_lt hn0,
    Nat.mod_eq_of_lt hn1, Nat.mod_eq_of_lt hn2,
    Nat.mod_eq_of_lt hNSM, Nat.mod_eq_of_lt hz0,
    Nat.mod_eq_of_lt hz1, Nat.mod_eq_of_lt hz2,
    Nat.mod_eq_of_lt hZSM, Nat.mod_eq_of_lt hStartM,
    Nat.mod_eq_of_lt hFinishM, Nat.mod_eq_of_lt hPowM,
    Nat.mod_eq_of_lt hEdgeM, Nat.mod_eq_of_lt hEdgeSuccM,
    Nat.mod_eq_of_lt hCursorM,
    Nat.mod_eq_of_lt hCompareM, Nat.mod_eq_of_lt hBadM,
    Nat.mod_eq_of_lt hNewM, Nat.mod_eq_of_lt hViolM,
    Nat.mod_eq_of_lt hViolOnlyM,
    h4M, h17M, h178M, h182M, h196M, h198M, hGridM, h131072M,
    rCurrentEdge, rCursor, rViol, rOK, rFlag, rA, rB, rC, rD,
    rBorrow, rLt, rEq, rEqBorrow, gridDepth, gridScale,
    and_assoc, or_assoc]
  try exact finish_flag _ viol hViolOnlyM hViolM

/-- One literal emitted row advances the source cursor and adds exactly one
failure bit.  The wide comparison and every scalar guard are connected here;
the theorem remains uniform in the transcript data. -/
theorem rowBody_run (r : EncodedRow) (k currentEdge cursor viol : Nat)
    (s : AState)
    (hEdge : s.regs rCurrentEdge = currentEdge)
    (hCursor : s.regs rCursor = cursor)
    (hViol : s.regs rViol = viol)
    (hWords : r.Words)
    (hEdgeM : currentEdge < M) (hEdgeSuccM : currentEdge + 1 < M)
    (hCursorM : cursor < M) (hViolM : viol + 1 < M) :
    let out := arun k s (rowBody r)
    out.regs rViol = viol + failureBit r currentEdge cursor ∧
      out.regs rCurrentEdge = r.edge ∧
      out.regs rCursor = r.finishGrid := by
  let compared := arun k (arun k s (comparePrelude r)) compareBody
  have hframe := compareStage_frame r k s
  dsimp only at hframe
  have hCompareLe : compared.regs rBorrow ≤ 1 :=
    compareStage_run_le_one r k s hWords
  have hCompare : compared.regs rBorrow = 1 ↔
      r.norm.val < r.limit.val :=
    compareStage_run_eq_one_iff r k s hWords
  have hguard := guardBody_run r k currentEdge cursor
    (compared.regs rBorrow) viol compared
    (hframe.1.trans hEdge)
    (hframe.2.1.trans hCursor)
    rfl
    (hframe.2.2.trans hViol)
    hWords hEdgeM hEdgeSuccM hCursorM hCompareLe hViolM
  dsimp only at hguard
  have hfail := one_sub_rowBit r currentEdge cursor
    (compared.regs rBorrow) hCompareLe hCompare
  have hout : arun k s (rowBody r) = arun k compared (guardBody r) := by
    simp [rowBody, arun_append, compared]
  rw [hout]
  exact ⟨hguard.2.1.trans (by rw [hfail]), hguard.2.2.1, hguard.2.2.2⟩

structure ScanState where
  edge : Nat
  cursor : Nat
  violations : Nat
  deriving Repr, DecidableEq

def scanStep (st : ScanState) (r : EncodedRow) : ScanState :=
  { edge := r.edge
    cursor := r.finishGrid
    violations := st.violations + failureBit r st.edge st.cursor }

def scanFrom (rows : List EncodedRow) (initial : ScanState) : ScanState :=
  rows.foldl scanStep initial

def scan (rows : List EncodedRow) (initialEdge initialCursor : Nat) : ScanState :=
  scanFrom rows
    { edge := initialEdge, cursor := initialCursor, violations := 0 }

def AllValidFrom : Nat → Nat → List EncodedRow → Prop
  | _, _, [] => True
  | edge, cursor, row :: rest =>
      row.ValidAfter edge cursor ∧
        AllValidFrom row.edge row.finishGrid rest

def RowsSafe (rows : List EncodedRow) : Prop :=
  ∀ r ∈ rows, r.Words ∧ r.edge + 1 < M

theorem failureBit_le_one (r : EncodedRow) (edge cursor : Nat) :
    failureBit r edge cursor ≤ 1 := by
  unfold failureBit
  split <;> omega

theorem failureBit_eq_zero_iff (r : EncodedRow) (edge cursor : Nat) :
    failureBit r edge cursor = 0 ↔ r.ValidAfter edge cursor := by
  simp [failureBit]

theorem scanFrom_violations_le (rows : List EncodedRow) (initial : ScanState) :
    (scanFrom rows initial).violations ≤ initial.violations + rows.length := by
  induction rows generalizing initial with
  | nil => simp [scanFrom]
  | cons row rest ih =>
      have hrest := ih (scanStep initial row)
      have hfail := failureBit_le_one row initial.edge initial.cursor
      change (scanFrom rest (scanStep initial row)).violations ≤
        initial.violations + (rest.length + 1)
      calc
        _ ≤ (scanStep initial row).violations + rest.length := hrest
        _ = initial.violations + failureBit row initial.edge initial.cursor +
            rest.length := by rfl
        _ ≤ initial.violations + (rest.length + 1) := by omega

theorem scanFrom_zero_iff (rows : List EncodedRow) (initial : ScanState) :
    (scanFrom rows initial).violations = 0 ↔
      initial.violations = 0 ∧
        AllValidFrom initial.edge initial.cursor rows := by
  induction rows generalizing initial with
  | nil => simp [scanFrom, AllValidFrom]
  | cons row rest ih =>
      change (scanFrom rest (scanStep initial row)).violations = 0 ↔
        initial.violations = 0 ∧
          AllValidFrom initial.edge initial.cursor (row :: rest)
      rw [ih (scanStep initial row)]
      simp [scanStep, AllValidFrom, failureBit_eq_zero_iff, and_assoc]

theorem scan_zero_iff (rows : List EncodedRow) (initialEdge initialCursor : Nat) :
    (scan rows initialEdge initialCursor).violations = 0 ↔
      AllValidFrom initialEdge initialCursor rows := by
  simpa [scan] using scanFrom_zero_iff rows
    { edge := initialEdge, cursor := initialCursor, violations := 0 }

set_option maxHeartbeats 1000000

/-- The emitted concatenation of row blocks is the ordinary mathematical
scan.  Only word-capacity side conditions occur; no row predicate is assumed. -/
theorem sweepBody_run (rows : List EncodedRow)
    (k initialEdge initialCursor viol : Nat) (s : AState)
    (hEdge : s.regs rCurrentEdge = initialEdge)
    (hCursor : s.regs rCursor = initialCursor)
    (hViol : s.regs rViol = viol)
    (hSafe : RowsSafe rows)
    (hEdgeM : initialEdge < M) (hEdgeSuccM : initialEdge + 1 < M)
    (hCursorM : initialCursor < M)
    (hCapacity : viol + rows.length < M) :
    let source := rows.foldl scanStep
      { edge := initialEdge, cursor := initialCursor, violations := viol }
    let out := arun k s (sweepBody rows)
    out.regs rCurrentEdge = source.edge ∧
      out.regs rCursor = source.cursor ∧
      out.regs rViol = source.violations := by
  induction rows generalizing s initialEdge initialCursor viol with
  | nil =>
      simpa [sweepBody, arun] using And.intro hEdge (And.intro hCursor hViol)
  | cons row rest ih =>
      have hrowSafe := hSafe row (by simp)
      rcases hrowSafe.1 with
        ⟨hREdgeM, _, _, _, _, _, _, _, _, _, _, _, hRFinishM, _⟩
      have hrestSafe : RowsSafe rest := by
        intro r hr
        exact hSafe r (by simp [hr])
      have hfailLe := failureBit_le_one row initialEdge initialCursor
      simp only [List.length_cons] at hCapacity
      have hnextCapacity :
          viol + failureBit row initialEdge initialCursor + rest.length < M := by
        omega
      have hrowCapacity : viol + 1 < M := by omega
      have hrow := rowBody_run row k initialEdge initialCursor viol s
        hEdge hCursor hViol hrowSafe.1 hEdgeM hEdgeSuccM hCursorM
        hrowCapacity
      let after := arun k s (rowBody row)
      have hrest := ih
        (initialEdge := row.edge) (initialCursor := row.finishGrid)
        (viol := viol + failureBit row initialEdge initialCursor) (s := after)
        hrow.2.1 hrow.2.2 hrow.1 hrestSafe
        hREdgeM hrowSafe.2 hRFinishM
        hnextCapacity
      dsimp only at hrest
      simpa [sweepBody, rowBody, arun_append, scanStep, after] using hrest

def endpointFailures (edge cursor finalEdge finalCursor : Nat) : Nat :=
  bit (edge ≠ finalEdge) + bit (cursor ≠ finalCursor)

theorem epilogueAt_run (k edge cursor viol finalEdge finalCursor : Nat)
    (s : AState)
    (hEdge : s.regs rCurrentEdge = edge)
    (hCursor : s.regs rCursor = cursor)
    (hViol : s.regs rViol = viol)
    (hEdgeM : edge < M) (hCursorM : cursor < M)
    (hFinalEdgeM : finalEdge < M) (hFinalCursorM : finalCursor < M)
    (hCapacity : viol + 2 < M) :
    (arun k s (epilogueAt finalEdge finalCursor)).regs rViol =
      viol + endpointFailures edge cursor finalEdge finalCursor := by
  have hEdge' : s.regs 12 = edge := by simpa [rCurrentEdge] using hEdge
  have hCursor' : s.regs 13 = cursor := by simpa [rCursor] using hCursor
  have hViol' : s.regs 14 = viol := by simpa [rViol] using hViol
  have hFinalEdgeMod : finalEdge % M = finalEdge := Nat.mod_eq_of_lt hFinalEdgeM
  have hFinalCursorMod : finalCursor % M = finalCursor :=
    Nat.mod_eq_of_lt hFinalCursorM
  have hViolM : viol < M := by omega
  have hViolOneM : viol + 1 < M := by omega
  by_cases he : edge = finalEdge <;> by_cases hc : cursor = finalCursor
  all_goals
    simp [epilogueAt, endpointFailures, bit, arun, astep, AState.writeReg,
      sdest, sval, denoteOperand, denoteOp, hEdge', hCursor', hViol', he, hc,
      Nat.mod_eq_of_lt hEdgeM, Nat.mod_eq_of_lt hCursorM,
      Nat.mod_eq_of_lt hFinalEdgeM, Nat.mod_eq_of_lt hFinalCursorM,
      hFinalEdgeMod, hFinalCursorMod, Nat.mod_eq_of_lt hViolM,
      Nat.mod_eq_of_lt hViolOneM, Nat.mod_eq_of_lt hCapacity,
      rCurrentEdge, rCursor, rViol, rA]
  all_goals simp [hEdge', hCursor', hViol', he, hc, hFinalEdgeMod,
    hFinalCursorMod, Nat.mod_eq_of_lt hViolM,
    Nat.mod_eq_of_lt hViolOneM, Nat.mod_eq_of_lt hCapacity]

def ScalarNoDiv : AInstr → Bool
  | .scalar instr => NoDivI instr
  | .load _ _ | .store _ _ => false

theorem allDefined_of_scalarNoDiv (xs : List AInstr) (len k : Nat) (s : AState)
    (h : xs.all ScalarNoDiv = true) : AllDefined len k s xs := by
  induction xs generalizing s with
  | nil => trivial
  | cons instr rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      constructor
      · cases instr with
        | scalar scalarInstr =>
            have hone :=
              LeanCompCert.Verified.ArrayScalarBlock.allDefined_lift_of_noDiv
                len k [scalarInstr] s (by simpa [ScalarNoDiv] using h.1)
            exact hone.1
        | load dest index => simp [ScalarNoDiv] at h
        | store index src => simp [ScalarNoDiv] at h
      · exact ih (astep k s instr) h.2

theorem rowBody_scalarNoDiv (r : EncodedRow) :
    (rowBody r).all ScalarNoDiv = true := by rfl

theorem rowBody_defined (r : EncodedRow) (len k : Nat) (s : AState) :
    AllDefined len k s (rowBody r) :=
  allDefined_of_scalarNoDiv _ len k s (rowBody_scalarNoDiv r)

theorem sweepBody_defined (rows : List EncodedRow) (len k : Nat) (s : AState) :
    AllDefined len k s (sweepBody rows) := by
  induction rows generalizing s with
  | nil => simp [sweepBody, AllDefined]
  | cons row rest ih =>
      rw [sweepBody, List.flatMap_cons, AllDefined_append]
      exact ⟨rowBody_defined row len k s,
        ih (arun k s (rowBody row))⟩

theorem programFrom_denote_exists (rows : List EncodedRow)
    (initialEdge initialCursor finalEdge finalCursor : Nat) :
    ∃ n,
      (programFrom rows initialEdge initialCursor finalEdge finalCursor).denote =
        some n := by
  let p := programFrom rows initialEdge initialCursor finalEdge finalCursor
  let entry := arun 0 initialAState p.init
  have hInit : denoteAInstrs p.arrayLen 0 initialAState p.init = some entry := by
    apply denoteAInstrs_eq_arun
    simp [p, programFrom, AllDefined, ADefined]
  have hDenote := AProgram.denote_eq_foldl_mem p (fun _ => True)
    (fun index s => arun index s p.body) (fun s => arun 0 s p.epilogue)
    entry hInit trivial
    (by
      intro index s _ _
      apply denoteAInstrs_eq_arun
      simpa [p, programFrom] using sweepBody_defined rows 1 index s)
    (by intros; trivial)
    (by
      intro s _
      apply denoteAInstrs_eq_arun
      exact allDefined_of_scalarNoDiv _ 1 0 s (by rfl))
  exact ⟨((arun 0
      ((List.range p.loopCount).foldl
        (fun s index => arun index s p.body) entry)
      p.epilogue).regs p.output), hDenote⟩

/-- An accepting source denotation of a bounded shard certifies every row and
both explicit shard endpoints.  Combined with `programFrom_compiled`, this is
the compiler-to-finite-certificate route used by production receipts. -/
theorem programFrom_denote_zero_sound (rows : List EncodedRow)
    (initialEdge initialCursor finalEdge finalCursor : Nat)
    (hSafe : RowsSafe rows)
    (hInitialEdgeM : initialEdge < M)
    (hInitialEdgeSuccM : initialEdge + 1 < M)
    (hInitialCursorM : initialCursor < M)
    (hFinalEdgeM : finalEdge < M) (hFinalCursorM : finalCursor < M)
    (hCapacity : rows.length + 2 < M)
    (hDenote :
      (programFrom rows initialEdge initialCursor finalEdge finalCursor).denote =
        some 0) :
    AllValidFrom initialEdge initialCursor rows ∧
      (scan rows initialEdge initialCursor).edge = finalEdge ∧
      (scan rows initialEdge initialCursor).cursor = finalCursor := by
  let p := programFrom rows initialEdge initialCursor finalEdge finalCursor
  let entry := arun 0 initialAState p.init
  let loopOut := arun 0 entry p.body
  let source := scan rows initialEdge initialCursor
  have hEntryEdge : entry.regs rCurrentEdge = initialEdge := by
    simp [entry, p, programFrom, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, rCurrentEdge, rCursor, rViol,
      Nat.mod_eq_of_lt hInitialEdgeM]
  have hEntryCursor : entry.regs rCursor = initialCursor := by
    simp [entry, p, programFrom, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, rCurrentEdge, rCursor, rViol,
      Nat.mod_eq_of_lt hInitialCursorM]
  have hEntryViol : entry.regs rViol = 0 := by
    simp [entry, p, programFrom, arun, astep, AState.writeReg, sdest, sval,
      denoteOperand, rCurrentEdge, rCursor, rViol]
  have hInitialRegs : ∀ j, initialAState.regs j < M := by
    intro j
    simp [initialAState, initialState, M]
  have hInitialArr : ∀ j, initialAState.arr j < M := by
    intro j
    simp [initialAState, M]
  have hEntryRegs : ∀ j, entry.regs j < M := by
    simpa [entry] using arun_regs_word 0 p.init initialAState
      hInitialRegs hInitialArr
  have hEntryArr : ∀ j, entry.arr j < M := by
    simpa [entry] using arun_arr_word 0 p.init initialAState
      hInitialRegs hInitialArr
  have hLoopRegs : ∀ j, loopOut.regs j < M := by
    simpa [loopOut] using arun_regs_word 0 p.body entry hEntryRegs hEntryArr
  have hRowsCapacity : rows.length < M := by omega
  have hSweep := sweepBody_run rows 0 initialEdge initialCursor 0 entry
    hEntryEdge hEntryCursor hEntryViol hSafe hInitialEdgeM
    hInitialEdgeSuccM hInitialCursorM (by simpa using hRowsCapacity)
  have hSweep' :
      loopOut.regs rCurrentEdge = source.edge ∧
        loopOut.regs rCursor = source.cursor ∧
        loopOut.regs rViol = source.violations := by
    simpa [loopOut, p, programFrom, source, scan, scanFrom] using hSweep
  have hSourceBound : source.violations ≤ rows.length := by
    simpa [source, scan] using
      (scanFrom_violations_le rows
        { edge := initialEdge, cursor := initialCursor, violations := 0 })
  have hSourceCapacity : source.violations + 2 < M := by omega
  have hEpilogue := epilogueAt_run 0 source.edge source.cursor
    source.violations finalEdge finalCursor loopOut
    hSweep'.1 hSweep'.2.1 hSweep'.2.2
    (by
      rw [← hSweep'.1]
      exact hLoopRegs rCurrentEdge)
    (by
      rw [← hSweep'.2.1]
      exact hLoopRegs rCursor)
    hFinalEdgeM hFinalCursorM hSourceCapacity
  have hTotal := AProgram.output_eq_arun_of_denote_eq_some p hDenote
  have hOutput :
      0 = (arun 0 loopOut (epilogueAt finalEdge finalCursor)).regs rViol := by
    simpa [p, programFrom, entry, loopOut] using hTotal
  have hzero :
      source.violations +
        endpointFailures source.edge source.cursor finalEdge finalCursor = 0 := by
    rw [hEpilogue] at hOutput
    exact hOutput.symm
  have hSourceZero : source.violations = 0 := by omega
  have hEndpoints : source.edge = finalEdge ∧ source.cursor = finalCursor := by
    have hend : endpointFailures source.edge source.cursor
        finalEdge finalCursor = 0 := by omega
    by_cases he : source.edge = finalEdge <;>
      by_cases hc : source.cursor = finalCursor <;>
      simp [endpointFailures, bit, he, hc] at hend ⊢
  have hValid : AllValidFrom initialEdge initialCursor rows := by
    apply (scan_zero_iff rows initialEdge initialCursor).mp
    simpa [source] using hSourceZero
  exact ⟨hValid, hEndpoints⟩

#print axioms comparePrelude_run
#print axioms compareStage_run_eq_one_iff
#print axioms guardBody_run
#print axioms rowBit_eq_one_iff
#print axioms rowBody_run
#print axioms sweepBody_run
#print axioms programFrom_denote_zero_sound

end LeanCompCert.Ports.A7BoundaryProgram

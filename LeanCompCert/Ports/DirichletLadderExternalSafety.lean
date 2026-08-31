import LeanCompCert.Ports.DirichletLadderExternalDenotation

/-!
# Fixed-width safety audit for an external Dirichlet ladder stream

The historical ladder program accumulates its failures with machine-word
addition.  That is adequate for the small executable regression tests, but is
not by itself a fail-closed production interface: an adversarially large
stream can wrap `rViol`, and several checks are made after a subtraction,
product, or address calculation has already taken place modulo `2^64`.

This file deliberately leaves that program unchanged.  It defines a small
independent audit whose failure bit is accumulated with `.bor`.  Acceptance of
the audit has only a fixed-width meaning; it does not assume or prove any GRH
or analytic statement.

The checked fields close four machine/reference seams:

* every `isLast` is a bit, so the following record's `1 - prevLast` is exact;
* `lower + slots`, `upper + 1`, and both Turing endpoint products cannot wrap;
* `q` and `blk` lie in the source production range, making the height products
  exact under the separate static campaign bound below;
* `conjFirst < records`, so `13 * conjFirst + 11` cannot wrap or alias once the
  array-size static bound holds.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.DirichletLadder

private abbrev I := AInstr

def bo (d : Nat) (o : Op) (a b : Operand) : I :=
  .scalar (.binop d o a b)

def rBad : Nat := 0
def rBadB : Nat := 1
def rBadC : Nat := 2
def maxQ : Nat := 400000

/-- Largest accepted upper zero count for which multiplication by the fixed
source Turing width is an exact `u64` multiplication. -/
def maxPinnedUpper : Nat := (M - 1) / hExpect - 1

/-- Static bounds on a production campaign.  They mention only the public
schedule size, never certificate contents. -/
structure StaticBounds (c : Cfg) : Prop where
  array_word : c.arrayLen < M
  height_product_word : 5 * c.records * maxQ < M

/-- One record's caller-owned words satisfy every fixed-width precondition
used by the historical arithmetic checker. -/
def RecordSafe (c : Cfg) (arr : Nat → Nat) (idx : Nat) : Prop :=
  let b := recW * idx
  let tag := arr b
  let blk := arr (b + 1)
  let lower := arr (b + 2)
  let slots := arr (b + 3)
  let upper := arr (b + 4)
  let isLast := arr (b + 7)
  let henc := arr (b + 9)
  let conjFirst := arr (b + 11)
  let q := tag >>> 20
  isLast ≤ 1 ∧
    lower ≤ maxPinnedUpper ∧
    slots ≤ maxPinnedUpper ∧
    upper ≤ maxPinnedUpper ∧
    henc ≤ hExpect ∧
    0 < q ∧ q ≤ maxQ ∧
    blk < c.records ∧
    conjFirst < c.records

/-- The safety statement decoded from an accepted audit. -/
def AllRecordsSafe (c : Cfg) (arr : Nat → Nat) : Prop :=
  ∀ idx, idx < c.records → RecordSafe c arr idx

/-- Load just the source fields needed by the fixed-width audit. -/
def loadBlock : List I :=
  [ bo 20 .mul .idx (.lit recW)
  , .load 21 20                                      -- tag
  , bo 20 .add (.reg 20) (.lit 1), .load 22 20       -- blk
  , bo 20 .add (.reg 20) (.lit 1), .load 23 20       -- lower
  , bo 20 .add (.reg 20) (.lit 1), .load 24 20       -- slots
  , bo 20 .add (.reg 20) (.lit 1), .load 25 20       -- upper
  , bo 20 .add (.reg 20) (.lit 1)
  , bo 20 .add (.reg 20) (.lit 1)
  , bo 20 .add (.reg 20) (.lit 1), .load 28 20       -- isLast
  , bo 20 .add (.reg 20) (.lit 1)
  , bo 20 .add (.reg 20) (.lit 1), .load 30 20       -- henc
  , bo 20 .add (.reg 20) (.lit 1)
  , bo 20 .add (.reg 20) (.lit 1), .load 32 20       -- conjFirst

  ]

/-- Framing/count fixed-width checks, split at sticky-lane state cuts so the
soundness proof never has to elaborate the whole production block at once. -/
def checkAIsLast : List I :=
  [ bo 33 .gt (.reg 28) (.lit 1)
  , bo rBad .bor (.reg rBad) (.reg 33) ]

def checkALower : List I :=
  [ bo 34 .gt (.reg 23) (.lit maxPinnedUpper)
  , bo rBad .bor (.reg rBad) (.reg 34) ]

def checkASlots : List I :=
  [ bo 35 .gt (.reg 24) (.lit maxPinnedUpper)
  , bo rBad .bor (.reg rBad) (.reg 35) ]

def checkA : List I := checkAIsLast ++ checkALower ++ checkASlots

/-- Turing endpoint and source-modulus fixed-width checks. -/
def checkBUpper : List I :=
  [ bo 36 .gt (.reg 25) (.lit maxPinnedUpper)
  , bo rBadB .bor (.reg rBadB) (.reg 36) ]

def checkBHeight : List I :=
  [ bo 37 .gt (.reg 30) (.lit hExpect)
  , bo rBadB .bor (.reg rBadB) (.reg 37) ]

def checkBQLoad : List I :=
  [ bo 39 .lshr (.reg 21) (.lit 20) ]

def checkBQZero : List I :=
  [ bo 40 .eq (.reg 39) (.lit 0)
  , bo rBadB .bor (.reg rBadB) (.reg 40)
  ]

def checkBQMax : List I :=
  [ bo 41 .gt (.reg 39) (.lit maxQ)
  , bo rBadB .bor (.reg rBadB) (.reg 41) ]

def checkBQ : List I := checkBQLoad ++ checkBQZero ++ checkBQMax

def checkB : List I := checkBUpper ++ checkBHeight ++ checkBQ

/-- Schedule/address checks depending on the public record count. -/
def checkCBlock (c : Cfg) : List I :=
  [ bo 42 .ge (.reg 22) (.lit c.records)
  , bo rBadC .bor (.reg rBadC) (.reg 42) ]

def checkCConj (c : Cfg) : List I :=
  [ bo 43 .ge (.reg 32) (.lit c.records)
  , bo rBadC .bor (.reg rBadC) (.reg 43) ]

def checkC (c : Cfg) : List I := checkCBlock c ++ checkCConj c

def checkBlock (c : Cfg) : List I := checkA ++ checkB ++ checkC c

/-- A compact sticky audit.  It uses only comparisons and loads; in
particular, it does not repeat the expensive ladder computation. -/
def guardBody (c : Cfg) : List I := loadBlock ++ checkBlock c

def finishB : List I := [bo rBad .bor (.reg rBad) (.reg rBadB)]
def finishC : List I := [bo rBad .bor (.reg rBad) (.reg rBadC)]
def finishBlock : List I := finishB ++ finishC

def program (c : Cfg) : AProgram :=
  { regCount := 44
    arrayLen := c.arrayLen
    loopCount := c.records
    init := []
    body := guardBody c
    epilogue := finishBlock
    output := rBad }

/-- Source specialization used by a production certificate. -/
def sourceProgram (records termDigest : Nat) : AProgram :=
  program (sourceCfg records termDigest)

private def operandWFB (r : Nat) : Operand → Bool
  | .reg i => decide (i < r)
  | _ => true

private def instrWFB (r : Nat) : Instr → Bool
  | .mov d s => decide (d < r) && operandWFB r s
  | .binop d _ l rr =>
      decide (d < r) && operandWFB r l && operandWFB r rr

private def ainstrWFB (r : Nat) : AInstr → Bool
  | .scalar i => instrWFB r i
  | .load d i => decide (d < r) && decide (i < r)
  | .store i s => decide (i < r) && decide (s < r)

private theorem operandWFB_correct {r : Nat} {o : Operand}
    (h : operandWFB r o = true) : o.WF r := by
  cases o with
  | reg i => exact of_decide_eq_true h
  | lit _ => trivial
  | idx => trivial

private theorem instrWFB_correct {r : Nat} {i : Instr}
    (h : instrWFB r i = true) : i.WF r := by
  cases i with
  | mov d s =>
      simp only [instrWFB, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1, operandWFB_correct h.2⟩
  | binop d op l rr =>
      simp only [instrWFB, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1.1, operandWFB_correct h.1.2,
        operandWFB_correct h.2⟩

private theorem ainstrWFB_correct {r : Nat} {a : AInstr}
    (h : ainstrWFB r a = true) : a.WF r := by
  cases a with
  | scalar i => exact instrWFB_correct h
  | load d i =>
      simp only [ainstrWFB, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩
  | store i s =>
      simp only [ainstrWFB, Bool.and_eq_true] at h
      exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

theorem program_wf (c : Cfg) : (program c).WF := by
  refine ⟨by show rBad < 44; decide, ?_, ?_, ?_⟩
  · simp [program]
  · intro a ha
    exact ainstrWFB_correct
      (List.all_eq_true.mp (show (guardBody c).all (ainstrWFB 44) = true by
        rfl) a ha)
  · intro a ha
    exact ainstrWFB_correct
      (List.all_eq_true.mp (show finishBlock.all (ainstrWFB 44) = true by
        rfl) a ha)

end LeanCompCert.Ports.DirichletLadderExternalSafety

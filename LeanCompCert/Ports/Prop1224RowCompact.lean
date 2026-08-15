import LeanCompCert.Ports.Prop1224RowExtension

/-!
# Compact nonempty-row stream for Proposition 12.2.4

The row verifier normally retains only its last bounded-memory window.  The
cell verifier, however, needs only rows whose proved window is nonempty.  This
module appends six words for each such row to a bounded compact stream:

`q, phiLo, constLo, afHi, kLo, kHi`, where
`afHi = ⌈ω*·7.284·f₁(q)·2^E⌉`.  The conversion from the row's
`f1Hi` word is part of the emitted program; it is not delegated to the host
that launches the cell checker.

`kLo` is the proved floor `varpiLo >> E`, not the oracle's floor-plus-one.
Capacity exhaustion increments the ordinary violation register before any
out-of-range store can occur.
-/

namespace LeanCompCert.Ports.Prop1224RowCompact

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve (ainstrWFB forall_wf_of_all all_append)
open LeanCompCert.Ports.Prop1224Row

def fields : Nat := 6

def rCompactCount : Nat := 542
def rHasRoom : Nat := 543

/-- Scratch words for the compiled `f1Hi ↦ afHi` conversion. -/
def rAfNum : Nat := 512
def rAfHi : Nat := 513
def rAfRem : Nat := 514

/-- Convert the row's upper `f₁(q)` word to the upper envelope-coefficient
word consumed by `CellCfg`.  Since the denominator is `2^E`, quotient and
remainder are a logical shift and mask; the block has no partial operation. -/
def afHiBlock : List AInstr :=
  [ .scalar (.binop rAfNum .mul (.lit kAHi) (.reg 334))
  , .scalar (.binop rAfHi .lshr (.reg rAfNum) (.lit E))
  , .scalar (.binop rAfRem .band (.reg rAfNum) (.lit (oneE - 1)))
  , .scalar (.binop rAfRem .ne (.reg rAfRem) (.lit 0))
  , .scalar (.binop rAfHi .add (.reg rAfHi) (.reg rAfRem)) ]

def compactBase (c : RowCfg) : Nat := c.arrayLen
def compactResult (c : RowCfg) (capacity : Nat) : Nat :=
  compactBase c + fields * capacity
def compactArrayLen (c : RowCfg) (capacity : Nat) : Nat :=
  compactResult c capacity + 1

/-! The shared-table pipeline needs the retained stream at a caller-selected
address, after all table planes.  These variants also accumulate the number of
cell iterations `sum (kHi - 1)` needed by a stream consumer. -/

def compactResultAt (base capacity : Nat) : Nat := base + fields * capacity
def compactCellCountAt (base capacity : Nat) : Nat := compactResultAt base capacity + 1
def compactArrayLenAt (base capacity : Nat) : Nat := compactCellCountAt base capacity + 1

def compactInitAt (c : RowCfg) (base capacity : Nat) : List AInstr :=
  c.init ++
  [ .scalar (.mov 500 (.lit (compactCellCountAt base capacity)))
  , .store 500 rZero ]

/-- Append the completed row if the proved source window `[kLo,kHi)` is
nonempty.  Registers 500--511 are dead after the base tail and are reused as
address/condition scratch. -/
def compactStoreBody (c : RowCfg) (capacity : Nat) : List AInstr :=
  let endR := endBase + c.slots - 1
  [ .scalar (.binop 500 .mul (.reg endR) (.reg 357))
  , .scalar (.binop rHasRoom .lt (.reg rCompactCount) (.lit capacity))
  , .scalar (.binop 501 .mul (.reg 500) (.reg rHasRoom))
  , .scalar (.binop 502 .sub (.lit 1) (.reg rHasRoom))
  , .scalar (.binop 502 .mul (.reg 500) (.reg 502))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 502)) ] ++ afHiBlock ++
  ([276, 337, 340, rAfHi, 355, 348].zipIdx.flatMap fun item =>
    gatedStore rCompactCount (compactBase c + item.2 * capacity)
      501 c.scratch 510 item.1) ++
  [ .scalar (.binop rCompactCount .add (.reg rCompactCount) (.reg 501)) ]

def compactStoreBodyAt (c : RowCfg) (base capacity : Nat) : List AInstr :=
  let endR := endBase + c.slots - 1
  [ .scalar (.binop 500 .mul (.reg endR) (.reg 357))
  , .scalar (.binop rHasRoom .lt (.reg rCompactCount) (.lit capacity))
  , .scalar (.binop 501 .mul (.reg 500) (.reg rHasRoom))
  , .scalar (.binop 502 .sub (.lit 1) (.reg rHasRoom))
  , .scalar (.binop 502 .mul (.reg 500) (.reg 502))
  , .scalar (.binop rViol .add (.reg rViol) (.reg 502)) ] ++ afHiBlock ++
  ([276, 337, 340, rAfHi, 355, 348].zipIdx.flatMap fun item =>
    gatedStore rCompactCount (base + item.2 * capacity)
      501 c.scratch 510 item.1) ++
  [ .scalar (.binop 500 .sub (.reg 348) (.lit 1))
  , .scalar (.binop 500 .mul (.reg 500) (.reg 501))
  , .scalar (.mov 502 (.lit (compactCellCountAt base capacity)))
  , .load 510 502
  , .scalar (.binop 510 .add (.reg 510) (.reg 500))
  , .store 502 510
  , .scalar (.binop rCompactCount .add (.reg rCompactCount) (.reg 501)) ]

def compactEpilogue (c : RowCfg) (capacity : Nat) : List AInstr :=
  c.epilogue ++
  [ .scalar (.mov 500 (.lit (compactResult c capacity)))
  , .store 500 rCompactCount ]

def compactEpilogueAt (c : RowCfg) (base capacity : Nat) : List AInstr :=
  c.epilogue ++
  [ .scalar (.mov 500 (.lit (compactResultAt base capacity)))
  , .store 500 rCompactCount ]

def denseCompactPrefixProgram (c : RowCfg) (rows capacity : Nat) : AProgram := {
  regCount := regCount
  arrayLen := compactArrayLen c capacity
  loopCount := c.prefixLoopCount rows
  init := c.init
  body := c.body ++ compactStoreBody c capacity
  epilogue := compactEpilogue c capacity
  output := outputReg
}

def extensionCompactPrefixProgram (c : RowCfg) (rows capacity : Nat) : AProgram := {
  regCount := regCount
  arrayLen := compactArrayLen c capacity
  loopCount := c.prefixLoopCount rows
  init := c.init
  body := Prop1224RowExtension.extensionBody c ++ compactStoreBody c capacity
  epilogue := compactEpilogue c capacity
  output := outputReg
}

def denseCompactPrefixProgramAt (c : RowCfg) (rows capacity base arrayLen : Nat) : AProgram := {
  regCount := regCount
  arrayLen := arrayLen
  loopCount := c.prefixLoopCount rows
  init := compactInitAt c base capacity
  body := c.body ++ compactStoreBodyAt c base capacity
  epilogue := compactEpilogueAt c base capacity
  output := outputReg
}

def extensionCompactPrefixProgramAt (c : RowCfg) (rows capacity base arrayLen : Nat) : AProgram := {
  regCount := regCount
  arrayLen := arrayLen
  loopCount := c.prefixLoopCount rows
  init := compactInitAt c base capacity
  body := Prop1224RowExtension.extensionBody c ++ compactStoreBodyAt c base capacity
  epilogue := compactEpilogueAt c base capacity
  output := outputReg
}

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem compactStoreBody_all (c : RowCfg) (capacity : Nat) :
    (compactStoreBody c capacity).all (ainstrWFB regCount) = true := by
  obtain ⟨lo, segLen, segCount, expUnroll, smallQ, markSteps, table⟩ := c
  cases smallQ <;> rfl

theorem compactEpilogue_all (c : RowCfg) (capacity : Nat) :
    (compactEpilogue c capacity).all (ainstrWFB regCount) = true := by
  exact all_append (epilogue_all c) (by rfl)

theorem compactInitAt_all (c : RowCfg) (base capacity : Nat) :
    (compactInitAt c base capacity).all (ainstrWFB regCount) = true := by
  exact all_append (init_all c) (by rfl)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem compactStoreBodyAt_all (c : RowCfg) (base capacity : Nat) :
    (compactStoreBodyAt c base capacity).all (ainstrWFB regCount) = true := by
  obtain ⟨lo, segLen, segCount, expUnroll, smallQ, markSteps, table⟩ := c
  cases smallQ <;> rfl

theorem compactEpilogueAt_all (c : RowCfg) (base capacity : Nat) :
    (compactEpilogueAt c base capacity).all (ainstrWFB regCount) = true := by
  exact all_append (epilogue_all c) (by rfl)

theorem denseCompactPrefixProgram_wf (c : RowCfg) (rows capacity : Nat) :
    (denseCompactPrefixProgram c rows capacity).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c),
   forall_wf_of_all (all_append (body_all c) (compactStoreBody_all c capacity)),
   forall_wf_of_all (compactEpilogue_all c capacity)⟩

theorem extensionCompactPrefixProgram_wf (c : RowCfg) (rows capacity : Nat) :
    (extensionCompactPrefixProgram c rows capacity).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c),
   forall_wf_of_all (all_append
     (Prop1224RowExtension.extensionBody_all c)
     (compactStoreBody_all c capacity)),
   forall_wf_of_all (compactEpilogue_all c capacity)⟩

theorem denseCompactPrefixProgramAt_wf (c : RowCfg)
    (rows capacity base arrayLen : Nat) :
    (denseCompactPrefixProgramAt c rows capacity base arrayLen).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (compactInitAt_all c base capacity),
   forall_wf_of_all (all_append (body_all c)
     (compactStoreBodyAt_all c base capacity)),
   forall_wf_of_all (compactEpilogueAt_all c base capacity)⟩

theorem extensionCompactPrefixProgramAt_wf (c : RowCfg)
    (rows capacity base arrayLen : Nat) :
    (extensionCompactPrefixProgramAt c rows capacity base arrayLen).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (compactInitAt_all c base capacity),
   forall_wf_of_all (all_append
     (Prop1224RowExtension.extensionBody_all c)
     (compactStoreBodyAt_all c base capacity)),
   forall_wf_of_all (compactEpilogueAt_all c base capacity)⟩

theorem denseCompactPrefixProgram_compiled (c : RowCfg) (rows capacity : Nat)
    (base : Int) (hBase : BaseOk
      (denseCompactPrefixProgram c rows capacity).arrayLen base)
    (n : Nat) (hDenote :
      (denseCompactPrefixProgram c rows capacity).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((denseCompactPrefixProgram c rows capacity).initialMCC base)
          (denseCompactPrefixProgram c rows capacity).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(denseCompactPrefixProgram c rows capacity).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (denseCompactPrefixProgram_wf c rows capacity)
    base hBase n hDenote

theorem extensionCompactPrefixProgram_compiled (c : RowCfg)
    (rows capacity : Nat) (base : Int) (hBase : BaseOk
      (extensionCompactPrefixProgram c rows capacity).arrayLen base)
    (n : Nat) (hDenote :
      (extensionCompactPrefixProgram c rows capacity).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((extensionCompactPrefixProgram c rows capacity).initialMCC base)
          (extensionCompactPrefixProgram c rows capacity).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(extensionCompactPrefixProgram c rows capacity).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (extensionCompactPrefixProgram_wf c rows capacity)
    base hBase n hDenote

theorem denseCompactPrefixProgramAt_compiled (c : RowCfg)
    (rows capacity streamBase arrayLen : Nat) (base : Int)
    (hBase : BaseOk arrayLen base) (n : Nat)
    (hDenote : (denseCompactPrefixProgramAt c rows capacity streamBase arrayLen).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((denseCompactPrefixProgramAt c rows capacity streamBase arrayLen).initialMCC base)
          (denseCompactPrefixProgramAt c rows capacity streamBase arrayLen).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(denseCompactPrefixProgramAt c rows capacity streamBase arrayLen).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _
    (denseCompactPrefixProgramAt_wf c rows capacity streamBase arrayLen)
    base hBase n hDenote

theorem extensionCompactPrefixProgramAt_compiled (c : RowCfg)
    (rows capacity streamBase arrayLen : Nat) (base : Int)
    (hBase : BaseOk arrayLen base) (n : Nat)
    (hDenote : (extensionCompactPrefixProgramAt c rows capacity streamBase arrayLen).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((extensionCompactPrefixProgramAt c rows capacity streamBase arrayLen).initialMCC base)
          (extensionCompactPrefixProgramAt c rows capacity streamBase arrayLen).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(extensionCompactPrefixProgramAt c rows capacity streamBase arrayLen).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _
    (extensionCompactPrefixProgramAt_wf c rows capacity streamBase arrayLen)
    base hBase n hDenote

#print axioms denseCompactPrefixProgram_compiled
#print axioms extensionCompactPrefixProgram_compiled
#print axioms denseCompactPrefixProgramAt_compiled
#print axioms extensionCompactPrefixProgramAt_compiled

end LeanCompCert.Ports.Prop1224RowCompact

import LeanCompCert.Ports.Prop1224Cell

/-!
# Shared compiled `phi` and squarefree table for Proposition 12.2.4

All cell rows use the same arithmetic functions of `r`.  Computing them once
through the verified segmented sieve avoids repeating a sieve for roughly
1.3 million nonempty `q` rows.  The output planes contain `phi(r)` and the
zero/one squarefree indicator for every requested `1 <= r <= rowCount`.
-/

namespace LeanCompCert.Ports.Prop1224PhiSquarefreeTable

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve (ainstrWFB forall_wf_of_all all_append)
open LeanCompCert.Ports.Prop1224Cell

def tablePeriod (c : CellCfg) : Nat := c.markSteps + c.segLen

def tablePrefixLoopCount (c : CellCfg) (rows : Nat) : Nat :=
  let full := rows / c.segLen
  let tail := rows % c.segLen
  full * tablePeriod c +
    if tail = 0 then 0 else c.markSteps + tail

def outputBase (c : CellCfg) : Nat := c.arrayLen
def phiBase (c : CellCfg) : Nat := outputBase c
def squarefreeBase (c : CellCfg) (rowCount : Nat) : Nat :=
  outputBase c + rowCount + 1
def outputResult (c : CellCfg) (rowCount : Nat) : Nat :=
  squarefreeBase c rowCount + rowCount + 1
def outputArrayLen (c : CellCfg) (rowCount : Nat) : Nat :=
  outputResult c rowCount + 1

def gatedStore (cell base cond scratch t src : Nat) : List AInstr :=
  [ .scalar (.binop t .add (.reg cell) (.lit base))
  , .scalar (.binop t .mul (.reg t) (.reg cond))
  , .scalar (.binop (t + 1) .sub (.lit 1) (.reg cond))
  , .scalar (.binop (t + 1) .mul (.reg (t + 1)) (.lit scratch))
  , .scalar (.binop t .add (.reg t) (.reg (t + 1)))
  , .store t src ]

/-- The first sixteen instructions of `accBody` decode exact `phi(r)` and the
squarefree bit.  Store them globally, then reset the three bounded-window
planes for reuse. -/
def tableAccBody (c : CellCfg) (rowCount : Nat) : List AInstr :=
  let L := c.segLen
  let SNK := c.sink
  c.accBody.take 16 ++
  gatedStore 85 (phiBase c) 12 SNK 300 98 ++
  gatedStore 85 (squarefreeBase c rowCount) 12 SNK 302 99 ++
  [ .scalar (.binop 304 .sub (.lit 1) (.reg 12))
  , .scalar (.binop 304 .mul (.reg 304) (.lit SNK))
  , .scalar (.binop 305 .add (.reg 86) (.reg 304))
  , .scalar (.binop 306 .add (.reg 305) (.lit L))
  , .scalar (.binop 307 .add (.reg 305) (.lit (2 * L)))
  , .store 305 rOne
  , .store 306 rOne
  , .store 307 rZero ]

def tableTailBody (c : CellCfg) : List AInstr :=
  let Pd := tablePeriod c
  let L := c.segLen
  [ .scalar (.binop 310 .add (.reg rR) (.lit 1))
  , .scalar (.binop 311 .eq (.reg 310) (.lit Pd))
  , .scalar (.binop 312 .sub (.lit 1) (.reg 311))
  , .scalar (.binop rR .mul (.reg 312) (.reg 310))
  , .scalar (.binop 313 .mul (.reg 311) (.lit L))
  , .scalar (.binop rW .add (.reg rW) (.reg 313)) ]

def tableBody (c : CellCfg) (rowCount : Nat) : List AInstr :=
  c.markBody ++ tableAccBody c rowCount ++ tableTailBody c

def tableEpilogue (c : CellCfg) (rowCount : Nat) : List AInstr :=
  [ .scalar (.mov 320 (.lit (outputResult c rowCount)))
  , .store 320 rViol ]

def tableProgram (c : CellCfg) (rowCount : Nat) : AProgram := {
  regCount := regCount
  arrayLen := outputArrayLen c rowCount
  loopCount := tablePrefixLoopCount c rowCount
  init := c.init { g := 0, ex := 0, th := 2, t := 0, cells := 0 }
  body := tableBody c rowCount
  epilogue := tableEpilogue c rowCount
  output := outputReg
}

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem tableAccBody_all (c : CellCfg) (rowCount : Nat) :
    (tableAccBody c rowCount).all (ainstrWFB regCount) = true := by
  obtain ⟨q, phiLo, constLo, afHi, kLo, kHi, qPrimes, lo, segLen,
    segCount, markSteps, table⟩ := c
  rfl

theorem tableTailBody_all (c : CellCfg) :
    (tableTailBody c).all (ainstrWFB regCount) = true := by rfl

theorem tableBody_all (c : CellCfg) (rowCount : Nat) :
    (tableBody c rowCount).all (ainstrWFB regCount) = true :=
  all_append (all_append (markBody_all c) (tableAccBody_all c rowCount))
    (tableTailBody_all c)

theorem tableEpilogue_all (c : CellCfg) (rowCount : Nat) :
    (tableEpilogue c rowCount).all (ainstrWFB regCount) = true := by rfl

theorem tableProgram_wf (c : CellCfg) (rowCount : Nat) :
    (tableProgram c rowCount).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c _),
   forall_wf_of_all (tableBody_all c rowCount),
   forall_wf_of_all (tableEpilogue_all c rowCount)⟩

theorem tableProgram_compiled (c : CellCfg) (rowCount : Nat) (base : Int)
    (hBase : BaseOk (tableProgram c rowCount).arrayLen base)
    (n : Nat) (hDenote : (tableProgram c rowCount).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((tableProgram c rowCount).initialMCC base)
          (tableProgram c rowCount).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(tableProgram c rowCount).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (tableProgram_wf c rowCount) base hBase n hDenote

#print axioms tableProgram_compiled

end LeanCompCert.Ports.Prop1224PhiSquarefreeTable

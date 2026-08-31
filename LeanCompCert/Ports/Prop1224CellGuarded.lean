import LeanCompCert.Ports.Prop1224CellObservation

/-!
# Fail-closed wrapper for the Proposition 12.2.4 cell program

The historical cell body counts its mathematical and schedule failures, but
two unsigned additions were justified only by source-side readiness premises:
the running `G_q` accumulator and the `G_q + envelope` comparison input.  This
module leaves that body byte-for-byte unchanged and surrounds it with fresh
registers which detect both wraps.

The returned verdict is a bitwise OR of every dedicated failure class.  Thus
zero cannot arise by cancellation or by overflow in a final aggregate sum.
The two new diagnostics are sticky OR bits and consequently need no counter
room premise.  Production evaluation remains entirely in the compiled
program; all definitions here are symbolic.
-/

namespace LeanCompCert.Ports.Prop1224CellGuarded

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
  (ainstrWFB forall_wf_of_all all_append)
open LeanCompCert.Ports.Prop1224Cell

/-! ## Fresh wrapper registers

The literal cell program uses registers only below `300`.  Keeping the wrapper
at and above that boundary makes its source-state projection structural.
-/

def sourceRegBound : Nat := 300

def rOldG : Nat := 300
def rOldCell : Nat := 301
def rAccGe : Nat := 302
def rAccFail : Nat := 303
def rSumAddr : Nat := 304
def rSumG : Nat := 305
def rSum : Nat := 306
def rSumGe : Nat := 307
def rSumFail : Nat := 308
def rGatedSumFail : Nat := 309
def rVAccWrap : Nat := 310
def rVSumWrap : Nat := 311
def rVerdict : Nat := 312
def rVMarginSeen : Nat := 313
def rVMarkSeen : Nat := 314
def rVLog2Seen : Nat := 315
def rVCbrtSeen : Nat := 316
def rVCbrtHiSeen : Nat := 317

/-- Save precisely the two source words needed after the complete body. -/
def guardPrelude : List AInstr :=
  [ .scalar (.mov rOldG (.reg rG))
  , .scalar (.mov rOldCell (.reg rCi)) ]

/-- Detect a wrapped accumulator addition, then detect a wrapped
`published-G + envelope` addition on an active final-round margin event.

For words `x,y < 2^64` with `y < 2^64`, a wrapped `(x+y) mod 2^64` is strictly
smaller than `x` whenever `y != 0`; when `y = 0` there is no wrap. -/
def guardSuffix (c : CellCfg) : List AInstr :=
  [ .scalar (.binop rAccGe .ge (.reg rG) (.reg rOldG))
  , .scalar (.binop rAccFail .sub (.lit 1) (.reg rAccGe))
  , .scalar (.binop rVAccWrap .bor (.reg rVAccWrap) (.reg rAccFail))
  , .scalar (.binop rSumAddr .add (.reg rOldCell) (.lit (3 * c.segLen)))
  , .load rSumG rSumAddr
  , .scalar (.binop rSum .add (.reg rSumG) (.reg 217))
  , .scalar (.binop rSumGe .ge (.reg rSum) (.reg rSumG))
  , .scalar (.binop rSumFail .sub (.lit 1) (.reg rSumGe))
  , .scalar (.binop rGatedSumFail .mul (.reg rSumFail) (.reg 223))
  , .scalar (.binop rVSumWrap .bor (.reg rVSumWrap) (.reg rGatedSumFail))
    -- Retain the literal per-body failure signals themselves.  Unlike the
    -- historical additive counters, these sticky latches cannot wrap back to
    -- zero during a long production shard.
  , .scalar (.binop rVMarginSeen .bor (.reg rVMarginSeen) (.reg 226))
  , .scalar (.binop rVMarkSeen .bor (.reg rVMarkSeen) (.reg 80))
  , .scalar (.binop rVLog2Seen .bor (.reg rVLog2Seen) (.reg 127))
  , .scalar (.binop rVCbrtSeen .bor (.reg rVCbrtSeen) (.reg 204))
  , .scalar (.binop rVCbrtHiSeen .bor (.reg rVCbrtHiSeen) (.reg 271)) ]

def guardedBody (c : CellCfg) : List AInstr :=
  guardPrelude ++ c.body ++ guardSuffix c

/-- OR, rather than add, all failure classes into the returned verdict. -/
def verdictBlock : List AInstr :=
  [ .scalar (.mov rVerdict (.reg rVMargin))
  , .scalar (.binop rVerdict .bor (.reg rVerdict) (.reg rVMark))
  , .scalar (.binop rVerdict .bor (.reg rVerdict) (.reg rVLog2))
  , .scalar (.binop rVerdict .bor (.reg rVerdict) (.reg rVCbrt))
  , .scalar (.binop rVerdict .bor (.reg rVerdict) (.reg rVCbrtHi))
  , .scalar (.binop rVerdict .bor (.reg rVerdict) (.reg rVAccWrap))
  , .scalar (.binop rVerdict .bor (.reg rVerdict) (.reg rVSumWrap))
  , .scalar (.binop rVerdict .bor (.reg rVerdict) (.reg rVMarginSeen))
  , .scalar (.binop rVerdict .bor (.reg rVerdict) (.reg rVMarkSeen))
  , .scalar (.binop rVerdict .bor (.reg rVerdict) (.reg rVLog2Seen))
  , .scalar (.binop rVerdict .bor (.reg rVerdict) (.reg rVCbrtSeen))
  , .scalar (.binop rVerdict .bor (.reg rVerdict) (.reg rVCbrtHiSeen)) ]

/-- Preserve the historical eleven result cells and append the two new sticky
diagnostics in slots eleven and twelve. -/
def guardedEpilogue (c : CellCfg) : List AInstr :=
  c.epilogue ++ storeResult c 11 rVAccWrap ++
    storeResult c 12 rVSumWrap ++ verdictBlock

def guardedProgram (c : CellCfg) (seed : CellSeed) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen + 2
  loopCount := c.period * c.segCount
  init := c.init seed
  body := guardedBody c
  epilogue := guardedEpilogue c
  output := rVerdict
}

/-! ## Compiler bridge -/

theorem guardPrelude_all :
    guardPrelude.all (ainstrWFB regCount) = true := by rfl

theorem guardSuffix_all (c : CellCfg) :
    (guardSuffix c).all (ainstrWFB regCount) = true := by rfl

theorem guardedBody_all (c : CellCfg) :
    (guardedBody c).all (ainstrWFB regCount) = true :=
  all_append (all_append guardPrelude_all (body_all c)) (guardSuffix_all c)

theorem verdictBlock_all :
    verdictBlock.all (ainstrWFB regCount) = true := by rfl

theorem guardedEpilogue_all (c : CellCfg) :
    (guardedEpilogue c).all (ainstrWFB regCount) = true :=
  all_append
    (all_append
      (all_append (epilogue_all c)
        (storeResult_all c 11 rVAccWrap (by decide)))
      (storeResult_all c 12 rVSumWrap (by decide)))
    verdictBlock_all

theorem guardedProgram_wf (c : CellCfg) (seed : CellSeed) :
    (guardedProgram c seed).WF :=
  ⟨show rVerdict < regCount by decide,
   forall_wf_of_all (init_all c seed),
   forall_wf_of_all (guardedBody_all c),
   forall_wf_of_all (guardedEpilogue_all c)⟩

/-- Forward CompCert signature theorem for the fail-closed program. -/
theorem guardedProgram_compiled (c : CellCfg) (seed : CellSeed) (base : Int)
    (hBase : BaseOk (guardedProgram c seed).arrayLen base)
    (n : Nat) (hDenote : (guardedProgram c seed).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((guardedProgram c seed).initialMCC base)
          (guardedProgram c seed).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(guardedProgram c seed).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (guardedProgram_wf c seed) base hBase n hDenote

#print axioms guardedProgram_compiled

end LeanCompCert.Ports.Prop1224CellGuarded

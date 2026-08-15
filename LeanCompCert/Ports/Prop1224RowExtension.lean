import LeanCompCert.Ports.Prop1224Row

/-!
# Sparse `210 | q` row producer for Proposition 12.2.4

The extension range is represented as `q = 210*m`.  The existing row sieve
factors consecutive `m` values.  Immediately after loading those planes, this
module folds in one extra factor of each of `2,3,5,7` and changes the row base
from `m` to `q`.  If a fixed prime already divides `m`, multiplying by it adds
`p` to the totient recurrence; otherwise it adds `p-1` and the missing
distinct-prime contributions to `L`, `f1`, and `omega`.

Thus the expensive extension has only 89,047,619 rows, not a dense sweep from
3.3 to 22 billion.
-/

namespace LeanCompCert.Ports.Prop1224RowExtension

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve (ainstrWFB forall_wf_of_all all_append)
open LeanCompCert.Ports.Prop1224Row

def qMultiplier : Nat := 210
def firstM : Nat := 15_714_286
def extensionRows : Nat := 89_047_619
def lastM : Nat := 104_761_904

def rM : Nat := 535
def rRem : Nat := 536
def rDivides : Nat := 537
def rAbsent : Nat := 538
def rFactor : Nat := 539
def rTmp0 : Nat := 540
def rTmp1 : Nat := 541

/-- Fold one additional fixed prime into the already loaded factor planes. -/
def fixedPrimeBody (p : Nat) : List AInstr :=
  let alo := lnLo p / p
  let ahi := cdivN (lnHi p) p
  let ff := f1FactorHi p
  [ -- whether this distinct prime was already present in m
    .scalar (.binop rRem .urem (.reg rM) (.lit p))
  , .scalar (.binop rDivides .eq (.reg rRem) (.lit 0))
  , .scalar (.binop rAbsent .sub (.lit 1) (.reg rDivides))
    -- the extra multiplicity in q = 210*m
  , .scalar (.binop 270 .mul (.reg 270) (.lit p))
  , .scalar (.binop rFactor .sub (.lit p) (.reg rAbsent))
  , .scalar (.binop 271 .mul (.reg 271) (.reg rFactor))
    -- distinct-prime terms are added only when p was absent from m
  , .scalar (.binop rTmp0 .mul (.reg rAbsent) (.lit alo))
  , .scalar (.binop 272 .add (.reg 272) (.reg rTmp0))
  , .scalar (.binop rTmp0 .mul (.reg rAbsent) (.lit ahi))
  , .scalar (.binop 273 .add (.reg 273) (.reg rTmp0))
    -- outward refolding of f1 at scale 2^E
  , .scalar (.binop rTmp0 .mul (.reg 274) (.lit ff))
  , .scalar (.binop rTmp0 .add (.reg rTmp0) (.lit (oneE - 1)))
  , .scalar (.binop rTmp0 .lshr (.reg rTmp0) (.lit E))
  , .scalar (.binop rTmp0 .mul (.reg rTmp0) (.reg rAbsent))
  , .scalar (.binop rTmp1 .mul (.reg 274) (.reg rDivides))
  , .scalar (.binop 274 .add (.reg rTmp0) (.reg rTmp1))
  , .scalar (.binop 275 .add (.reg 275) (.reg rAbsent)) ]

def fixed210Body : List AInstr :=
  fixedPrimeBody 2 ++ fixedPrimeBody 3 ++ fixedPrimeBody 5 ++ fixedPrimeBody 7

/-- The first 18 base instructions load and neutralize the six factor planes;
the next four form the ordinary consecutive `q`.  Replace only those four,
leaving the logarithm/exponential slot decoder byte-for-byte shared. -/
def extensionDeriveBody (c : RowCfg) : List AInstr :=
  c.deriveBody.take 18 ++
  [ .scalar (.binop rM .add (.reg rW) (.reg rCi)) ] ++
  fixed210Body ++
  [ .scalar (.binop 276 .mul (.reg rM) (.lit qMultiplier))
  , .scalar (.binop 277 .udiv (.reg 276) (.reg 270))
  , .scalar (.binop 278 .ne (.reg 270) (.reg 276))
  , .scalar (.binop 307 .add (.reg 276) (.lit 1)) ] ++
  c.deriveBody.drop 22

def extensionBody (c : RowCfg) : List AInstr :=
  c.markBody ++ extensionDeriveBody c ++ logEngine c.expUnroll ++
    expEngine c.expUnroll ++ c.latchBody ++ c.finishBody ++ c.tailBody

def extensionPrefixProgram (c : RowCfg) (rows : Nat) : AProgram := {
  regCount := regCount
  arrayLen := c.arrayLen
  loopCount := c.prefixLoopCount rows
  init := c.init
  body := extensionBody c
  epilogue := c.epilogue
  output := outputReg
}

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem fixedPrimeBody_all (p : Nat) :
    (fixedPrimeBody p).all (ainstrWFB regCount) = true := by rfl

theorem fixed210Body_all :
    fixed210Body.all (ainstrWFB regCount) = true := by
  simp only [fixed210Body]
  exact all_append (all_append (all_append (fixedPrimeBody_all 2)
    (fixedPrimeBody_all 3)) (fixedPrimeBody_all 5)) (fixedPrimeBody_all 7)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem extensionDeriveBody_all (c : RowCfg) :
    (extensionDeriveBody c).all (ainstrWFB regCount) = true := by
  obtain ⟨lo, segLen, segCount, expUnroll, smallQ, markSteps, table⟩ := c
  cases smallQ <;> rfl

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem extensionBody_all (c : RowCfg) :
    (extensionBody c).all (ainstrWFB regCount) = true :=
  all_append (all_append (all_append (all_append (all_append (all_append
    (markBody_all c) (extensionDeriveBody_all c)) (logEngine_all _))
    (expEngine_all _)) (latchBody_all c)) (finishBody_all c)) (tailBody_all c)

theorem extensionPrefixProgram_wf (c : RowCfg) (rows : Nat) :
    (extensionPrefixProgram c rows).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (init_all c),
   forall_wf_of_all (extensionBody_all c),
   forall_wf_of_all (epilogue_all c)⟩

theorem extensionPrefixProgram_compiled (c : RowCfg) (rows : Nat) (base : Int)
    (hBase : BaseOk (extensionPrefixProgram c rows).arrayLen base)
    (n : Nat) (hDenote : (extensionPrefixProgram c rows).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((extensionPrefixProgram c rows).initialMCC base)
          (extensionPrefixProgram c rows).compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨(extensionPrefixProgram c rows).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (extensionPrefixProgram_wf c rows)
    base hBase n hDenote

theorem extension_endpoint :
    qMultiplier * (firstM + extensionRows - 1) = 21_999_999_840 := by decide

#print axioms extensionPrefixProgram_compiled

end LeanCompCert.Ports.Prop1224RowExtension

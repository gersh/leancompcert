import LeanCompCert.Ports.PsiRuntimePrimeTable

/-!
# Compiled construction of the psi prime-power table

This stage consumes the resident prime table and enumerates powers `p^k`,
`k >= 2`, entirely in compiled code.  It writes `(q,p)` pairs into the region
later consumed as `(q, lnFix p)`.  A following compiled fixed-log stage will
replace the second component.  The sort here is deliberately simple: the
number of prime powers per production shard is small, and a fixed bubble-sort
schedule is easy to refine without any data-dependent control flow.

The reserved `ppCount` is a capacity, not a value computed by Lean.  Overflow
is returned as a nonzero verdict.  Unused pairs have `q = 0`; the comparator
treats those as infinity, leaving all live pairs in increasing order at the
front of the table.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

def ppPowerRounds : Nat := 48

def ppQ : Nat := 360
def ppWrite : Nat := 361
def ppOverflow : Nat := 362

/-- One `(prime index, exponent)` point.  Safe multiplication is expressed by
`q <= hi / p`, so no wrapped product can be mistaken for an in-range power. -/
def psiPPGenerateBody (m : PsiRuntimeMeta) : List AInstr :=
  [ .scalar (.binop 10 .udiv .idx (.lit ppPowerRounds))
  , .scalar (.binop 11 .urem .idx (.lit ppPowerRounds))
  , .scalar (.binop 12 .eq (.reg 11) (.lit 0))
  , .scalar (.binop 13 .add (.reg 10) (.lit m.cfg.primeBase))
  , .load 14 13
  , .scalar (.binop 15 .sub (.lit 1) (.reg 12))
  , .scalar (.binop 16 .mul (.reg 12) (.reg 14))
  , .scalar (.binop 17 .mul (.reg 15) (.reg ppQ))
  , .scalar (.binop 18 .add (.reg 16) (.reg 17))
  , .scalar (.binop 19 .eq (.reg 14) (.lit 0))
  , .scalar (.binop 20 .add (.reg 14) (.reg 19))
  , .scalar (.binop 21 .udiv (.lit m.cfg.hi) (.reg 20))
  , .scalar (.binop 22 .le (.reg 18) (.reg 21))
  , .scalar (.binop 23 .mul (.reg 18) (.reg 14))
  , .scalar (.binop 24 .mul (.reg 22) (.reg 23))
  , .scalar (.binop 25 .sub (.lit 1) (.reg 22))
  , .scalar (.binop 26 .mul (.reg 25) (.lit (m.cfg.hi + 1)))
  , .scalar (.binop ppQ .add (.reg 24) (.reg 26))
  , .scalar (.binop 27 .ge (.reg ppQ) (.lit m.cfg.lo))
  , .scalar (.binop 28 .le (.reg ppQ) (.lit m.cfg.hi))
  , .scalar (.binop 29 .mul (.reg 27) (.reg 28))
  , .scalar (.binop 30 .lt (.reg ppWrite) (.lit m.ppCount))
  , .scalar (.binop 31 .mul (.reg 29) (.reg 30))
  , .scalar (.binop 32 .sub (.reg 29) (.reg 31))
  , .scalar (.binop ppOverflow .add (.reg ppOverflow) (.reg 32))
  , .scalar (.binop 33 .shl (.reg ppWrite) (.lit 1))
  , .scalar (.binop 34 .add (.reg 33) (.lit m.cfg.ppBase))
  , .scalar (.binop 35 .mul (.reg 31) (.reg 34))
  , .scalar (.binop 36 .sub (.lit 1) (.reg 31))
  , .scalar (.binop 37 .mul (.reg 36) (.lit m.markSink))
  , .scalar (.binop 38 .add (.reg 35) (.reg 37))
  , .store 38 ppQ
  , .scalar (.binop 39 .add (.reg 38) (.lit 1))
  , .store 39 14
  , .scalar (.binop ppWrite .add (.reg ppWrite) (.reg 31)) ]

def psiPPGenerateInit : List AInstr :=
  seedRegs [(ppQ, 0), (ppWrite, 0), (ppOverflow, 0)]

def psiPPGenerateProgram (m : PsiRuntimeMeta) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := m.primeCount * ppPowerRounds
    init := psiPPGenerateInit
    body := psiPPGenerateBody m
    epilogue := []
    output := ppOverflow }

theorem psiPPGenerateBody_all (m : PsiRuntimeMeta) :
    (psiPPGenerateBody m).all (ainstrWFB regCount) = true := by rfl

theorem psiPPGenerateProgram_wf (m : PsiRuntimeMeta) :
    (psiPPGenerateProgram m).WF :=
  ⟨show ppOverflow < regCount by decide, forall_wf_of_all (by rfl),
    forall_wf_of_all (psiPPGenerateBody_all m), forall_wf_of_all (by rfl)⟩

/-! ## Fixed-schedule pair sorting -/

/-- Compare adjacent pairs.  `q = 0` denotes an unused slot and orders after
every live (positive) prime power. -/
def psiPPSortBody (m : PsiRuntimeMeta) : List AInstr :=
  let width := max 1 (m.ppCount - 1)
  [ .scalar (.binop 10 .urem .idx (.lit width))
  , .scalar (.binop 11 .shl (.reg 10) (.lit 1))
  , .scalar (.binop 12 .add (.reg 11) (.lit m.cfg.ppBase))
  , .load 13 12
  , .scalar (.binop 14 .add (.reg 12) (.lit 1))
  , .load 15 14
  , .scalar (.binop 16 .add (.reg 12) (.lit 2))
  , .load 17 16
  , .scalar (.binop 18 .add (.reg 12) (.lit 3))
  , .load 19 18
  , .scalar (.binop 20 .eq (.reg 13) (.lit 0))
  , .scalar (.binop 21 .gt (.reg 17) (.lit 0))
  , .scalar (.binop 22 .mul (.reg 20) (.reg 21))
  , .scalar (.binop 23 .gt (.reg 13) (.reg 17))
  , .scalar (.binop 24 .gt (.reg 17) (.lit 0))
  , .scalar (.binop 25 .mul (.reg 23) (.reg 24))
  , .scalar (.binop 26 .add (.reg 22) (.reg 25))
  , .scalar (.binop 27 .sub (.lit 1) (.reg 26))
  , .scalar (.binop 28 .mul (.reg 26) (.reg 17))
  , .scalar (.binop 29 .mul (.reg 27) (.reg 13))
  , .scalar (.binop 30 .add (.reg 28) (.reg 29))
  , .scalar (.binop 31 .mul (.reg 26) (.reg 19))
  , .scalar (.binop 32 .mul (.reg 27) (.reg 15))
  , .scalar (.binop 33 .add (.reg 31) (.reg 32))
  , .scalar (.binop 34 .mul (.reg 26) (.reg 13))
  , .scalar (.binop 35 .mul (.reg 27) (.reg 17))
  , .scalar (.binop 36 .add (.reg 34) (.reg 35))
  , .scalar (.binop 37 .mul (.reg 26) (.reg 15))
  , .scalar (.binop 38 .mul (.reg 27) (.reg 19))
  , .scalar (.binop 39 .add (.reg 37) (.reg 38))
  , .store 12 30
  , .store 14 33
  , .store 16 36
  , .store 18 39 ]

def psiPPSortProgram (m : PsiRuntimeMeta) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := m.ppCount * (m.ppCount - 1)
    init := []
    body := psiPPSortBody m
    epilogue := []
    output := 0 }

theorem psiPPSortBody_all (m : PsiRuntimeMeta) :
    (psiPPSortBody m).all (ainstrWFB regCount) = true := by rfl

theorem psiPPSortProgram_wf (m : PsiRuntimeMeta) :
    (psiPPSortProgram m).WF := by
  unfold psiPPSortProgram
  refine ⟨show 0 < regCount by decide, ?_,
    forall_wf_of_all (psiPPSortBody_all m), ?_⟩
  · intro a h
    cases h
  · intro a h
    cases h

/-! ## Compiled logarithm weights

The generated table temporarily stores `(q,p)`.  Two fixed-schedule programs
replace `p` by `lnFix sc p`.  The first computes `floor(log2 p)` into the
cleared root-mark scratch.  The second performs exactly `sc` verified
fixed-log squaring rounds and the same `ln 2` conversion used by the main psi
program. -/

def ppExpRounds : Nat := 32
def ppEx : Nat := 360
def ppTh : Nat := 361
def ppXm : Nat := 362
def ppAa : Nat := 363

def psiPPExponentBody (m : PsiRuntimeMeta) : List AInstr :=
  [ .scalar (.binop 10 .udiv .idx (.lit ppExpRounds))
  , .scalar (.binop 11 .urem .idx (.lit ppExpRounds))
  , .scalar (.binop 12 .eq (.reg 11) (.lit 0))
  , .scalar (.binop 13 .add (.reg 11) (.lit 1))
  , .scalar (.binop 14 .eq (.reg 13) (.lit ppExpRounds))
  , .scalar (.binop 15 .shl (.reg 10) (.lit 1))
  , .scalar (.binop 16 .add (.reg 15) (.lit m.cfg.ppBase))
  , .scalar (.binop 17 .add (.reg 16) (.lit 1))
  , .load 18 17
  , .scalar (.binop 19 .gt (.reg 18) (.lit 0))
  , .scalar (.binop 20 .sub (.lit 1) (.reg 12))
  , .scalar (.binop 21 .mul (.reg 12) (.lit 1))
  , .scalar (.binop 22 .mul (.reg 20) (.reg ppEx))
  , .scalar (.binop 23 .add (.reg 21) (.reg 22))
  , .scalar (.binop 24 .mul (.reg 12) (.lit 4))
  , .scalar (.binop 25 .mul (.reg 20) (.reg ppTh))
  , .scalar (.binop 26 .add (.reg 24) (.reg 25))
  , .scalar (.binop 27 .ge (.reg 18) (.reg 26))
  , .scalar (.binop ppEx .add (.reg 23) (.reg 27))
  , .scalar (.binop 28 .mul (.reg 27) (.reg 26))
  , .scalar (.binop ppTh .add (.reg 26) (.reg 28))
  , .scalar (.binop 29 .mul (.reg 14) (.reg 19))
  , .scalar (.binop 30 .add (.reg 10) (.lit m.markBase))
  , .scalar (.binop 31 .mul (.reg 29) (.reg 30))
  , .scalar (.binop 32 .sub (.lit 1) (.reg 29))
  , .scalar (.binop 33 .mul (.reg 32) (.lit m.markSink))
  , .scalar (.binop 34 .add (.reg 31) (.reg 33))
  , .store 34 ppEx ]

def psiPPExponentProgram (m : PsiRuntimeMeta) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := m.ppCount * ppExpRounds
    init := seedRegs [(ppEx, 1), (ppTh, 4)]
    body := psiPPExponentBody m
    epilogue := []
    output := 0 }

theorem psiPPExponentBody_all (m : PsiRuntimeMeta) :
    (psiPPExponentBody m).all (ainstrWFB regCount) = true := by rfl

theorem psiPPExponentProgram_wf (m : PsiRuntimeMeta) :
    (psiPPExponentProgram m).WF := by
  unfold psiPPExponentProgram
  refine ⟨show 0 < regCount by decide, forall_wf_of_all (by rfl),
    forall_wf_of_all (psiPPExponentBody_all m), ?_⟩
  intro a h
  cases h

def psiPPLogBody (m : PsiRuntimeMeta) : List AInstr :=
  let S := max 1 m.cfg.sc
  [ .scalar (.binop 10 .udiv .idx (.lit S))
  , .scalar (.binop 11 .urem .idx (.lit S))
  , .scalar (.binop 12 .eq (.reg 11) (.lit 0))
  , .scalar (.binop 13 .add (.reg 11) (.lit 1))
  , .scalar (.binop 14 .eq (.reg 13) (.lit m.cfg.sc))
  , .scalar (.binop 15 .shl (.reg 10) (.lit 1))
  , .scalar (.binop 16 .add (.reg 15) (.lit m.cfg.ppBase))
  , .scalar (.binop 17 .add (.reg 16) (.lit 1))
  , .load 18 17
  , .scalar (.binop 19 .gt (.reg 18) (.lit 0))
  , .scalar (.binop 20 .add (.reg 10) (.lit m.markBase))
  , .load 21 20
  , .scalar (.binop 22 .sub (.lit 62) (.reg 21))
  , .scalar (.binop 23 .band (.reg 22) (.lit 63))
  , .scalar (.binop 24 .shl (.reg 18) (.reg 23))
  , .scalar (.binop 25 .sub (.lit 1) (.reg 12))
  , .scalar (.binop 26 .mul (.reg 12) (.reg 24))
  , .scalar (.binop 27 .mul (.reg 25) (.reg ppXm))
  , .scalar (.binop ppXm .add (.reg 26) (.reg 27))
  , .scalar (.binop ppAa .mul (.reg ppAa) (.reg 25))
    -- one exact fixed-log squaring round
  , .scalar (.binop 28 .lshr (.reg ppXm) (.lit 32))
  , .scalar (.binop 29 .band (.reg ppXm) (.lit 4294967295))
  , .scalar (.binop 30 .mul (.reg 28) (.reg 28))
  , .scalar (.binop 31 .mul (.reg 28) (.reg 29))
  , .scalar (.binop 32 .mul (.reg 29) (.reg 29))
  , .scalar (.binop 33 .lshr (.reg 31) (.lit 29))
  , .scalar (.binop 34 .band (.reg 31) (.lit 536870911))
  , .scalar (.binop 35 .lshr (.reg 32) (.lit 62))
  , .scalar (.binop 36 .band (.reg 32) (.lit 4611686018427387903))
  , .scalar (.binop 37 .shl (.reg 34) (.lit 33))
  , .scalar (.binop 38 .add (.reg 37) (.reg 36))
  , .scalar (.binop 39 .ge (.reg 38) (.lit 4611686018427387904))
  , .scalar (.binop 40 .shl (.reg 30) (.lit 2))
  , .scalar (.binop 41 .add (.reg 40) (.reg 33))
  , .scalar (.binop 42 .add (.reg 41) (.reg 35))
  , .scalar (.binop 43 .add (.reg 42) (.reg 39))
  , .scalar (.binop 44 .ge (.reg 43) (.lit 9223372036854775808))
  , .scalar (.binop ppXm .lshr (.reg 43) (.reg 44))
  , .scalar (.binop 45 .shl (.reg ppAa) (.lit 1))
  , .scalar (.binop ppAa .add (.reg 45) (.reg 44))
    -- convert `(ex << S) + aa` from log2 to natural log
  , .scalar (.binop 46 .shl (.reg 21) (.lit m.cfg.sc))
  , .scalar (.binop 47 .add (.reg 46) (.reg ppAa))
  , .scalar (.binop 48 .band (.reg 47) (.lit 4294967295))
  , .scalar (.binop 49 .lshr (.reg 47) (.lit 32))
  , .scalar (.binop 50 .mul (.reg 48) (.lit L2lo))
  , .scalar (.binop 51 .mul (.reg 48) (.lit L2hi))
  , .scalar (.binop 52 .mul (.reg 49) (.lit L2lo))
  , .scalar (.binop 53 .mul (.reg 49) (.lit L2hi))
  , .scalar (.binop 54 .lshr (.reg 50) (.lit 32))
  , .scalar (.binop 55 .add (.reg 51) (.reg 52))
  , .scalar (.binop 56 .add (.reg 55) (.reg 54))
  , .scalar (.binop 57 .lshr (.reg 56) (.lit 32))
  , .scalar (.binop 58 .add (.reg 53) (.reg 57))
  , .scalar (.binop 59 .mul (.reg 14) (.reg 19))
  , .scalar (.binop 60 .mul (.reg 59) (.reg 17))
  , .scalar (.binop 61 .sub (.lit 1) (.reg 59))
  , .scalar (.binop 62 .mul (.reg 61) (.lit m.markSink))
  , .scalar (.binop 63 .add (.reg 60) (.reg 62))
  , .store 63 58 ]

def psiPPLogProgram (m : PsiRuntimeMeta) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := m.ppCount * m.cfg.sc
    init := seedRegs [(ppXm, 0), (ppAa, 0)]
    body := psiPPLogBody m
    epilogue := []
    output := 0 }

theorem psiPPLogBody_all (m : PsiRuntimeMeta) :
    (psiPPLogBody m).all (ainstrWFB regCount) = true := by rfl

theorem psiPPLogProgram_wf (m : PsiRuntimeMeta) :
    (psiPPLogProgram m).WF := by
  unfold psiPPLogProgram
  refine ⟨show 0 < regCount by decide, forall_wf_of_all (by rfl),
    forall_wf_of_all (psiPPLogBody_all m), ?_⟩
  intro a h
  cases h

theorem psiPPGenerateProgram_compiled (m : PsiRuntimeMeta) (base : Int)
    (hBase : BaseOk (psiPPGenerateProgram m).arrayLen base)
    (n : Nat) (hDenote : (psiPPGenerateProgram m).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiPPGenerateProgram m).initialMCC base)
          (psiPPGenerateProgram m).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiPPGenerateProgram m).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiPPGenerateProgram_wf m) base hBase n hDenote

theorem psiPPSortProgram_compiled (m : PsiRuntimeMeta) (base : Int)
    (hBase : BaseOk (psiPPSortProgram m).arrayLen base)
    (n : Nat) (hDenote : (psiPPSortProgram m).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiPPSortProgram m).initialMCC base)
          (psiPPSortProgram m).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiPPSortProgram m).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiPPSortProgram_wf m) base hBase n hDenote

theorem psiPPExponentProgram_compiled (m : PsiRuntimeMeta) (base : Int)
    (hBase : BaseOk (psiPPExponentProgram m).arrayLen base)
    (n : Nat) (hDenote : (psiPPExponentProgram m).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiPPExponentProgram m).initialMCC base)
          (psiPPExponentProgram m).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiPPExponentProgram m).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiPPExponentProgram_wf m) base hBase n hDenote

theorem psiPPLogProgram_compiled (m : PsiRuntimeMeta) (base : Int)
    (hBase : BaseOk (psiPPLogProgram m).arrayLen base)
    (n : Nat) (hDenote : (psiPPLogProgram m).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiPPLogProgram m).initialMCC base)
          (psiPPLogProgram m).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiPPLogProgram m).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiPPLogProgram_wf m) base hBase n hDenote

#print axioms psiPPGenerateProgram_wf
#print axioms psiPPSortProgram_wf
#print axioms psiPPExponentProgram_wf
#print axioms psiPPLogProgram_wf
#print axioms psiPPGenerateProgram_compiled
#print axioms psiPPSortProgram_compiled
#print axioms psiPPExponentProgram_compiled
#print axioms psiPPLogProgram_compiled

/-! Small differential constants only.  These keep the compiled smoke output
anchored to `lnFix`; they are not a production table or range fold. -/

example : lnFix 48 11 = 674947516065513 := by decide
example : lnFix 48 5 = 453016498919635 := by decide
example : lnFix 48 2 = 195103586505167 := by decide
example : lnFix 48 13 = 721969060655497 := by decide

end LeanCompCert.Ports.PsiSegSieve

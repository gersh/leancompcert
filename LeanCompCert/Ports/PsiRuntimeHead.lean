import LeanCompCert.Ports.PsiRuntimePrimePowers

/-!
# Compiled psi head/carry construction

The legacy emitter evaluated `psiHead` in Lean.  The runtime route instead
uses the resident prime table.  It computes `lnFix sc p` once for each prime,
then visits the fixed grid `(p,k)` and accumulates one copy for every
`p^k <= root`.  Thus the compiled fold is exactly the finite identity

`psi(root) = sum_{p^k <= root} log p`.

For the first production shard `lo = root + 1`; the resulting result cells
are loaded directly by `psiRuntimeProgramFromHead`.  No production prefix
list, prime-power list, or head fold is evaluated by Lean, and no literal seed
has to be copied out of the executable and back into an emitter.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

def primeEx : Nat := 360
def primeTh : Nat := 361
def primeXm : Nat := 362
def primeAa : Nat := 363
def headQ : Nat := 364

/-! ## `floor(log2 p)` for every resident prime -/

def psiPrimeExponentBody (m : PsiRuntimeMeta) : List AInstr :=
  [ .scalar (.binop 10 .udiv .idx (.lit ppExpRounds))
  , .scalar (.binop 11 .urem .idx (.lit ppExpRounds))
  , .scalar (.binop 12 .eq (.reg 11) (.lit 0))
  , .scalar (.binop 13 .add (.reg 11) (.lit 1))
  , .scalar (.binop 14 .eq (.reg 13) (.lit ppExpRounds))
  , .scalar (.binop 15 .add (.reg 10) (.lit m.cfg.primeBase))
  , .load 16 15
  , .scalar (.binop 17 .sub (.lit 1) (.reg 12))
  , .scalar (.binop 18 .mul (.reg 12) (.lit 1))
  , .scalar (.binop 19 .mul (.reg 17) (.reg primeEx))
  , .scalar (.binop 20 .add (.reg 18) (.reg 19))
  , .scalar (.binop 21 .mul (.reg 12) (.lit 4))
  , .scalar (.binop 22 .mul (.reg 17) (.reg primeTh))
  , .scalar (.binop 23 .add (.reg 21) (.reg 22))
  , .scalar (.binop 24 .ge (.reg 16) (.reg 23))
  , .scalar (.binop primeEx .add (.reg 20) (.reg 24))
  , .scalar (.binop 25 .mul (.reg 24) (.reg 23))
  , .scalar (.binop primeTh .add (.reg 23) (.reg 25))
  , .scalar (.binop 26 .mul (.reg 14) (.reg 10))
  , .scalar (.binop 27 .add (.reg 26) (.lit m.markBase))
  , .scalar (.binop 28 .sub (.lit 1) (.reg 14))
  , .scalar (.binop 29 .mul (.reg 28) (.lit m.markSink))
  , .scalar (.binop 30 .mul (.reg 14) (.reg 27))
  , .scalar (.binop 31 .add (.reg 30) (.reg 29))
  , .store 31 primeEx ]

def psiPrimeExponentProgram (m : PsiRuntimeMeta) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := m.primeCount * ppExpRounds
    init := seedRegs [(primeEx, 1), (primeTh, 4)]
    body := psiPrimeExponentBody m
    epilogue := []
    output := 0 }

theorem psiPrimeExponentBody_all (m : PsiRuntimeMeta) :
    (psiPrimeExponentBody m).all (ainstrWFB regCount) = true := by rfl

theorem psiPrimeExponentProgram_wf (m : PsiRuntimeMeta) :
    (psiPrimeExponentProgram m).WF := by
  unfold psiPrimeExponentProgram
  refine ⟨show 0 < regCount by decide, forall_wf_of_all (by rfl),
    forall_wf_of_all (psiPrimeExponentBody_all m), ?_⟩
  intro a h
  cases h

/-! ## Exact fixed-log weights in scratch -/

def psiPrimeLogBody (m : PsiRuntimeMeta) : List AInstr :=
  let S := max 1 m.cfg.sc
  [ .scalar (.binop 10 .udiv .idx (.lit S))
  , .scalar (.binop 11 .urem .idx (.lit S))
  , .scalar (.binop 12 .eq (.reg 11) (.lit 0))
  , .scalar (.binop 13 .add (.reg 11) (.lit 1))
  , .scalar (.binop 14 .eq (.reg 13) (.lit m.cfg.sc))
  , .scalar (.binop 15 .add (.reg 10) (.lit m.cfg.primeBase))
  , .load 16 15
  , .scalar (.binop 17 .add (.reg 10) (.lit m.markBase))
  , .load 18 17
  , .scalar (.binop 19 .sub (.lit 62) (.reg 18))
  , .scalar (.binop 20 .band (.reg 19) (.lit 63))
  , .scalar (.binop 21 .shl (.reg 16) (.reg 20))
  , .scalar (.binop 22 .sub (.lit 1) (.reg 12))
  , .scalar (.binop 23 .mul (.reg 12) (.reg 21))
  , .scalar (.binop 24 .mul (.reg 22) (.reg primeXm))
  , .scalar (.binop primeXm .add (.reg 23) (.reg 24))
  , .scalar (.binop primeAa .mul (.reg primeAa) (.reg 22))
  , .scalar (.binop 25 .lshr (.reg primeXm) (.lit 32))
  , .scalar (.binop 26 .band (.reg primeXm) (.lit 4294967295))
  , .scalar (.binop 27 .mul (.reg 25) (.reg 25))
  , .scalar (.binop 28 .mul (.reg 25) (.reg 26))
  , .scalar (.binop 29 .mul (.reg 26) (.reg 26))
  , .scalar (.binop 30 .lshr (.reg 28) (.lit 29))
  , .scalar (.binop 31 .band (.reg 28) (.lit 536870911))
  , .scalar (.binop 32 .lshr (.reg 29) (.lit 62))
  , .scalar (.binop 33 .band (.reg 29) (.lit 4611686018427387903))
  , .scalar (.binop 34 .shl (.reg 31) (.lit 33))
  , .scalar (.binop 35 .add (.reg 34) (.reg 33))
  , .scalar (.binop 36 .ge (.reg 35) (.lit 4611686018427387904))
  , .scalar (.binop 37 .shl (.reg 27) (.lit 2))
  , .scalar (.binop 38 .add (.reg 37) (.reg 30))
  , .scalar (.binop 39 .add (.reg 38) (.reg 32))
  , .scalar (.binop 40 .add (.reg 39) (.reg 36))
  , .scalar (.binop 41 .ge (.reg 40) (.lit 9223372036854775808))
  , .scalar (.binop primeXm .lshr (.reg 40) (.reg 41))
  , .scalar (.binop 42 .shl (.reg primeAa) (.lit 1))
  , .scalar (.binop primeAa .add (.reg 42) (.reg 41))
  , .scalar (.binop 43 .shl (.reg 18) (.lit m.cfg.sc))
  , .scalar (.binop 44 .add (.reg 43) (.reg primeAa))
  , .scalar (.binop 45 .band (.reg 44) (.lit 4294967295))
  , .scalar (.binop 46 .lshr (.reg 44) (.lit 32))
  , .scalar (.binop 47 .mul (.reg 45) (.lit L2lo))
  , .scalar (.binop 48 .mul (.reg 45) (.lit L2hi))
  , .scalar (.binop 49 .mul (.reg 46) (.lit L2lo))
  , .scalar (.binop 50 .mul (.reg 46) (.lit L2hi))
  , .scalar (.binop 51 .lshr (.reg 47) (.lit 32))
  , .scalar (.binop 52 .add (.reg 48) (.reg 49))
  , .scalar (.binop 53 .add (.reg 52) (.reg 51))
  , .scalar (.binop 54 .lshr (.reg 53) (.lit 32))
  , .scalar (.binop 55 .add (.reg 50) (.reg 54))
  , .scalar (.mov 56 (.reg 14))
  , .scalar (.binop 57 .sub (.lit 1) (.reg 14))
  , .scalar (.binop 58 .mul (.reg 57) (.lit m.markSink))
  , .scalar (.binop 59 .mul (.reg 56) (.reg 17))
  , .scalar (.binop 60 .add (.reg 59) (.reg 58))
  , .store 60 55 ]

def psiPrimeLogProgram (m : PsiRuntimeMeta) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := m.primeCount * m.cfg.sc
    init := seedRegs [(primeXm, 0), (primeAa, 0)]
    body := psiPrimeLogBody m
    epilogue := []
    output := 0 }

theorem psiPrimeLogBody_all (m : PsiRuntimeMeta) :
    (psiPrimeLogBody m).all (ainstrWFB regCount) = true := by rfl

theorem psiPrimeLogProgram_wf (m : PsiRuntimeMeta) :
    (psiPrimeLogProgram m).WF := by
  unfold psiPrimeLogProgram
  refine ⟨show 0 < regCount by decide, forall_wf_of_all (by rfl),
    forall_wf_of_all (psiPrimeLogBody_all m), ?_⟩
  intro a h
  cases h

/-! ## Prime-power head fold -/

def headBase (m : PsiRuntimeMeta) : Nat :=
  biasOf m.cfg.sc - 2 ^ m.cfg.sc * m.root

def psiHeadFoldBody (m : PsiRuntimeMeta) : List AInstr :=
  [ .scalar (.binop 10 .udiv .idx (.lit ppPowerRounds))
  , .scalar (.binop 11 .urem .idx (.lit ppPowerRounds))
  , .scalar (.binop 12 .eq (.reg 11) (.lit 0))
  , .scalar (.binop 13 .add (.reg 10) (.lit m.cfg.primeBase))
  , .load 14 13
  , .scalar (.binop 15 .add (.reg 10) (.lit m.markBase))
  , .load 16 15
  , .scalar (.binop 17 .sub (.lit 1) (.reg 12))
  , .scalar (.binop 18 .mul (.reg 12) (.reg 14))
  , .scalar (.binop 19 .mul (.reg 17) (.reg headQ))
  , .scalar (.binop 20 .add (.reg 18) (.reg 19))
  , .scalar (.binop 21 .udiv (.lit m.root) (.reg 14))
  , .scalar (.binop 22 .le (.reg 20) (.reg 21))
  , .scalar (.binop 23 .mul (.reg 20) (.reg 14))
  , .scalar (.binop 24 .mul (.reg 22) (.reg 23))
  , .scalar (.binop 25 .sub (.lit 1) (.reg 22))
  , .scalar (.binop 26 .mul (.reg 25) (.lit (m.root + 1)))
  , .scalar (.binop 27 .add (.reg 24) (.reg 26))
  , .scalar (.binop 28 .mul (.reg 17) (.reg 27))
  , .scalar (.binop 29 .add (.reg 18) (.reg 28))
  , .scalar (.mov headQ (.reg 29))
  , .scalar (.binop 30 .le (.reg headQ) (.lit m.root))
  , .scalar (.binop 31 .mul (.reg 30) (.reg 16))
    -- add one live logarithm to the two-word accumulator
  , .scalar (.binop 32 .add (.reg rDlo) (.reg 31))
  , .scalar (.binop 33 .lt (.reg 32) (.reg rDlo))
  , .scalar (.mov rDlo (.reg 32))
  , .scalar (.binop rDhi .add (.reg rDhi) (.reg 33))
  , .scalar (.binop rTerms .add (.reg rTerms) (.reg 30)) ]

def psiHeadFoldInit (m : PsiRuntimeMeta) : List AInstr :=
  let b := headBase m
  let sq := Nat.sqrt m.root
  let ex := Nat.log2 m.cfg.lo
  seedRegs
    [(rDlo, b % 18446744073709551616),
     (rDhi, b / 18446744073709551616),
     (rPrev, m.root), (rTerms, 0), (rSq, sq), (rSq2, (sq + 1) * (sq + 1)),
     (rEx, ex), (rTh, 2 ^ (ex + 1)), (headQ, 0)]

def psiHeadFoldEpilogue (m : PsiRuntimeMeta) : List AInstr :=
  storeResult m.cfg 0 rDlo ++ storeResult m.cfg 1 rDhi ++
  storeResult m.cfg 2 rPrev ++ storeResult m.cfg 3 rTerms ++
  storeResult m.cfg 4 rSq ++ storeResult m.cfg 5 rEx ++
  storeResult m.cfg 6 rTh

def psiHeadFoldProgram (m : PsiRuntimeMeta) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := m.primeCount * ppPowerRounds
    init := psiHeadFoldInit m
    body := psiHeadFoldBody m
    epilogue := psiHeadFoldEpilogue m
    output := rTerms }

theorem psiHeadFoldBody_all (m : PsiRuntimeMeta) :
    (psiHeadFoldBody m).all (ainstrWFB regCount) = true := by rfl

theorem psiHeadFoldInit_all (m : PsiRuntimeMeta) :
    (psiHeadFoldInit m).all (ainstrWFB regCount) = true := by rfl

theorem psiHeadFoldProgram_wf (m : PsiRuntimeMeta) :
    (psiHeadFoldProgram m).WF :=
  ⟨show rTerms < regCount by decide,
   forall_wf_of_all (psiHeadFoldInit_all m),
   forall_wf_of_all (psiHeadFoldBody_all m),
   forall_wf_of_all (by
      apply all_append (all_append (all_append (all_append (all_append
        (all_append (storeResult_all m.cfg 0 rDlo (by decide))
          (storeResult_all m.cfg 1 rDhi (by decide)))
          (storeResult_all m.cfg 2 rPrev (by decide)))
          (storeResult_all m.cfg 3 rTerms (by decide)))
          (storeResult_all m.cfg 4 rSq (by decide)))
          (storeResult_all m.cfg 5 rEx (by decide)))
          (storeResult_all m.cfg 6 rTh (by decide)))⟩

/-! ## Load the compiled carry without copying it through Lean -/

def loadHeadResult (c : PsiCfg) (slot reg : Nat) : List AInstr :=
  [ .scalar (.mov 90 (.lit (c.resultBase + slot))), .load reg 90 ]

/-- Reconstruct the successor-square cursor from the carried integer square
root.  Keeping this derived word out of the carry cells prevents a second,
independently signed representation of the same state. -/
def psiHeadSquareReload : List AInstr :=
  [ .scalar (.binop 92 .add (.reg rSq) (.lit 1))
  , .scalar (.binop 93 .mul (.reg 92) (.reg 92))
  , .scalar (.mov rSq2 (.reg 93)) ]

def psiHeadLoadInit (c : PsiCfg) : List AInstr :=
  seedRegs [(rW, 1), (rWrite, c.primeBase + c.bootCount)] ++
  loadHeadResult c 0 rDlo ++ loadHeadResult c 1 rDhi ++
  loadHeadResult c 2 rPrev ++ loadHeadResult c 3 rTerms ++
  loadHeadResult c 4 rSq ++ loadHeadResult c 5 rEx ++
  loadHeadResult c 6 rTh ++ psiHeadSquareReload

def psiRuntimeProgramFromHead (m : PsiRuntimeMeta) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := m.cfg.period * m.cfg.segCount
    init := psiHeadLoadInit m.cfg
    body := m.cfg.body
    epilogue := m.cfg.epilogue
    output := outputReg }

theorem loadHeadResult_all (c : PsiCfg) (slot reg : Nat)
    (h : reg < regCount) :
    (loadHeadResult c slot reg).all (ainstrWFB regCount) = true := by
  have h90 : 90 < regCount := by decide
  simp [loadHeadResult, ainstrWFB, instrWFB, operandWFB, h, h90]

theorem psiHeadLoadInit_all (c : PsiCfg) :
    (psiHeadLoadInit c).all (ainstrWFB regCount) = true := by
  have hseed :
      (seedRegs [(rW, 1), (rWrite, c.primeBase + c.bootCount)]).all
        (ainstrWFB regCount) = true := by rfl
  simp only [psiHeadLoadInit, List.all_append, hseed, Bool.true_and,
    loadHeadResult_all c 0 rDlo (by decide),
    loadHeadResult_all c 1 rDhi (by decide),
    loadHeadResult_all c 2 rPrev (by decide),
    loadHeadResult_all c 3 rTerms (by decide),
    loadHeadResult_all c 4 rSq (by decide),
    loadHeadResult_all c 5 rEx (by decide),
    loadHeadResult_all c 6 rTh (by decide)]
  decide

theorem psiRuntimeProgramFromHead_wf (m : PsiRuntimeMeta) :
    (psiRuntimeProgramFromHead m).WF :=
  ⟨show outputReg < regCount by decide,
   forall_wf_of_all (psiHeadLoadInit_all m.cfg),
   forall_wf_of_all (body_all m.cfg),
   forall_wf_of_all (epilogue_all m.cfg)⟩

theorem psiPrimeExponentProgram_compiled (m : PsiRuntimeMeta) (base : Int)
    (hBase : BaseOk (psiPrimeExponentProgram m).arrayLen base)
    (n : Nat) (hDenote : (psiPrimeExponentProgram m).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiPrimeExponentProgram m).initialMCC base)
          (psiPrimeExponentProgram m).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiPrimeExponentProgram m).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiPrimeExponentProgram_wf m) base hBase n hDenote

theorem psiPrimeLogProgram_compiled (m : PsiRuntimeMeta) (base : Int)
    (hBase : BaseOk (psiPrimeLogProgram m).arrayLen base)
    (n : Nat) (hDenote : (psiPrimeLogProgram m).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiPrimeLogProgram m).initialMCC base)
          (psiPrimeLogProgram m).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiPrimeLogProgram m).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiPrimeLogProgram_wf m) base hBase n hDenote

theorem psiHeadFoldProgram_compiled (m : PsiRuntimeMeta) (base : Int)
    (hBase : BaseOk (psiHeadFoldProgram m).arrayLen base)
    (n : Nat) (hDenote : (psiHeadFoldProgram m).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiHeadFoldProgram m).initialMCC base)
          (psiHeadFoldProgram m).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiHeadFoldProgram m).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiHeadFoldProgram_wf m) base hBase n hDenote

theorem psiRuntimeProgramFromHead_compiled (m : PsiRuntimeMeta) (base : Int)
    (hBase : BaseOk (psiRuntimeProgramFromHead m).arrayLen base)
    (n : Nat) (hDenote : (psiRuntimeProgramFromHead m).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiRuntimeProgramFromHead m).initialMCC base)
          (psiRuntimeProgramFromHead m).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiRuntimeProgramFromHead m).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiRuntimeProgramFromHead_wf m) base hBase n hDenote

#print axioms psiPrimeExponentProgram_wf
#print axioms psiPrimeLogProgram_wf
#print axioms psiHeadFoldProgram_wf
#print axioms psiRuntimeProgramFromHead_wf
#print axioms psiPrimeExponentProgram_compiled
#print axioms psiPrimeLogProgram_compiled
#print axioms psiHeadFoldProgram_compiled
#print axioms psiRuntimeProgramFromHead_compiled

end LeanCompCert.Ports.PsiSegSieve

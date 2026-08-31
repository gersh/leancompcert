import LeanCompCert.Ports.PsiSegSieve
import LeanCompCert.Verified.ArrayPipeline

/-!
# Compiled construction of the psi prime table

Production `PsiCfg.ofScale` is deliberately not used here: it enumerates
primes and prime powers in Lean.  A runtime configuration contains only scalar
metadata.  The two programs below construct the resident prime table in
CompCert-compiled code before the main psi sweep:

1. a finite candidate/divisor grid marks composites;
2. a finite candidate scan appends precisely the unmarked candidates.

The root mark plane is placed after the result cells and is cleared by the
packer.  The later prime-power constructor may reuse that space.  Lean emits
only a fixed straight-line body plus scalar loop bounds; it never evaluates a
production-sized list or fold.
-/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

/-- Scalar metadata for a runtime-built psi shard.  `cfg.base.rootCount = 0`
keeps the resident-table main sweep out of the legacy in-program root phase.
The counts are receipts produced by compiled setup runs, not values normalized
by Lean. -/
structure PsiRuntimeMeta where
  cfg : PsiCfg
  root : Nat
  divCap : Nat
  primeCount : Nat
  /-- Reserved prime-power pair capacity.  Runtime generation must report no
  overflow; unused entries remain zero and sort after live entries. -/
  ppCount : Nat
  deriving Repr

/-- Build a table-free configuration from scalar metadata only. -/
def PsiRuntimeMeta.ofScalars (lo segLen segCount sc markSteps streamCap root
    divCap primeCount ppCount : Nat) : PsiRuntimeMeta :=
  { cfg :=
      { base :=
          { lo := lo
            segLen := segLen
            segCount := segCount
            rootCount := 0
            bootPrimes := [2]
            mainCount := primeCount
            rootCap := root
            markSteps := markSteps }
        sc := sc
        streamCap := streamCap
        pp := []
        ppLenOverride := some ppCount }
    root := root
    divCap := divCap
    primeCount := primeCount
    ppCount := ppCount }

def PsiRuntimeMeta.markBase (m : PsiRuntimeMeta) : Nat :=
  m.cfg.resultBase + 17

def PsiRuntimeMeta.markSink (m : PsiRuntimeMeta) : Nat :=
  m.markBase + m.root + 1

/-- Shared-array size for the runtime setup.  The prime-power generator writes
an inactive `(q,p)` pair at `markSink` and `markSink + 1`, so both cells must
be resident.  Earlier setup stages use only the first sink cell. -/
def PsiRuntimeMeta.arrayLen (m : PsiRuntimeMeta) : Nat := m.markSink + 2

/-! ## Stage one: compiled composite marking -/

def psiRootMarkDecode (m : PsiRuntimeMeta) : List AInstr :=
  let width := max 1 (m.divCap - 1)
  [ .scalar (.binop 10 .udiv .idx (.lit width))
  , .scalar (.binop 11 .add (.reg 10) (.lit 2))
  , .scalar (.binop 12 .urem .idx (.lit width))
  , .scalar (.binop 13 .add (.reg 12) (.lit 2)) ]

def psiRootMarkWitness : List AInstr :=
  [ .scalar (.binop 14 .mul (.reg 13) (.reg 13))
  , .scalar (.binop 15 .le (.reg 14) (.reg 11))
  , .scalar (.binop 16 .urem (.reg 11) (.reg 13))
  , .scalar (.binop 17 .eq (.reg 16) (.lit 0)) ]

def psiRootMarkTarget (m : PsiRuntimeMeta) : List AInstr :=
  [ .scalar (.binop 18 .mul (.reg 15) (.reg 17))
  , .scalar (.binop 19 .add (.reg 11) (.lit m.markBase))
  , .scalar (.binop 20 .mul (.reg 18) (.reg 19))
  , .scalar (.binop 21 .sub (.lit 1) (.reg 18))
  , .scalar (.binop 22 .mul (.reg 21) (.lit m.markSink))
  , .scalar (.binop 23 .add (.reg 20) (.reg 22)) ]

def psiRootMarkBody (m : PsiRuntimeMeta) : List AInstr :=
  psiRootMarkDecode m ++ psiRootMarkWitness ++ psiRootMarkTarget m ++
    [.store 23 18]

def psiRootMarkProgram (m : PsiRuntimeMeta) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := (m.root - 1) * (m.divCap - 1)
    init := []
    body := psiRootMarkBody m
    epilogue := [.scalar (.mov 0 (.lit 0))]
    output := 0 }

theorem psiRootMarkBody_all (m : PsiRuntimeMeta) :
    (psiRootMarkBody m).all (ainstrWFB regCount) = true := by rfl

theorem psiRootMarkProgram_wf (m : PsiRuntimeMeta) :
    (psiRootMarkProgram m).WF := by
  unfold psiRootMarkProgram
  refine ⟨show 0 < regCount by decide, ?_,
    forall_wf_of_all (psiRootMarkBody_all m), forall_wf_of_all (by rfl)⟩
  intro a h
  cases h

/-! ## Stage two: compiled table packing -/

def psiRootPackBody (m : PsiRuntimeMeta) : List AInstr :=
  [ .scalar (.binop 10 .add .idx (.lit 2))
  , .scalar (.binop 11 .add (.reg 10) (.lit m.markBase))
  , .load 12 11
  , .scalar (.binop 13 .eq (.reg 12) (.lit 0))
  , .scalar (.binop 14 .add (.reg rWrite) (.lit m.cfg.primeBase))
  , .scalar (.binop 15 .mul (.reg 13) (.reg 14))
  , .scalar (.binop 16 .sub (.lit 1) (.reg 13))
  , .scalar (.binop 17 .mul (.reg 16) (.lit m.markSink))
  , .scalar (.binop 18 .add (.reg 15) (.reg 17))
  , .store 18 10
  , .scalar (.binop rWrite .add (.reg rWrite) (.reg 13))
  , .store 11 rZero ]

def psiRootPackInit : List AInstr :=
  seedRegs [(rWrite, 0), (rZero, 0)]

def psiRootPackEpilogue (m : PsiRuntimeMeta) : List AInstr :=
  [ .scalar (.binop 10 .add (.reg rWrite) (.lit m.cfg.primeBase))
  , .scalar (.mov 11 (.lit m.cfg.sentinel))
  , .store 10 11 ]

def psiRootPackProgram (m : PsiRuntimeMeta) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := m.root - 1
    init := psiRootPackInit
    body := psiRootPackBody m
    epilogue := psiRootPackEpilogue m
    output := rWrite }

theorem psiRootPackBody_all (m : PsiRuntimeMeta) :
    (psiRootPackBody m).all (ainstrWFB regCount) = true := by rfl

theorem psiRootPackProgram_wf (m : PsiRuntimeMeta) :
    (psiRootPackProgram m).WF :=
  ⟨show rWrite < regCount by decide, forall_wf_of_all (by rfl),
    forall_wf_of_all (psiRootPackBody_all m), forall_wf_of_all (by rfl)⟩

/-! ## Main sweep over the resident tables -/

def psiRuntimeProgram (m : PsiRuntimeMeta) (s : PsiSeed) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := m.cfg.period * m.cfg.segCount
    init := seedRegs (m.cfg.seedList s)
    body := m.cfg.body
    epilogue := m.cfg.epilogue
    output := outputReg }

theorem psiRuntimeProgram_wf (m : PsiRuntimeMeta) (s : PsiSeed) :
    (psiRuntimeProgram m s).WF :=
  ⟨show outputReg < regCount by decide,
    forall_wf_of_all (seedRegs_all _ (seedList_ok m.cfg s)),
    forall_wf_of_all (body_all m.cfg),
    forall_wf_of_all (epilogue_all m.cfg)⟩

theorem psiRootMarkProgram_compiled (m : PsiRuntimeMeta) (base : Int)
    (hBase : BaseOk (psiRootMarkProgram m).arrayLen base)
    (n : Nat) (hDenote : (psiRootMarkProgram m).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiRootMarkProgram m).initialMCC base)
          (psiRootMarkProgram m).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiRootMarkProgram m).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiRootMarkProgram_wf m) base hBase n hDenote

theorem psiRootPackProgram_compiled (m : PsiRuntimeMeta) (base : Int)
    (hBase : BaseOk (psiRootPackProgram m).arrayLen base)
    (n : Nat) (hDenote : (psiRootPackProgram m).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiRootPackProgram m).initialMCC base)
          (psiRootPackProgram m).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiRootPackProgram m).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiRootPackProgram_wf m) base hBase n hDenote

theorem psiRuntimeProgram_compiled (m : PsiRuntimeMeta) (s : PsiSeed)
    (base : Int) (hBase : BaseOk (psiRuntimeProgram m s).arrayLen base)
    (n : Nat) (hDenote : (psiRuntimeProgram m s).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiRuntimeProgram m s).initialMCC base)
          (psiRuntimeProgram m s).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiRuntimeProgram m s).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiRuntimeProgram_wf m s) base hBase n hDenote

#print axioms psiRootMarkProgram_wf
#print axioms psiRootPackProgram_wf
#print axioms psiRuntimeProgram_wf
#print axioms psiRootMarkProgram_compiled
#print axioms psiRootPackProgram_compiled
#print axioms psiRuntimeProgram_compiled

end LeanCompCert.Ports.PsiSegSieve

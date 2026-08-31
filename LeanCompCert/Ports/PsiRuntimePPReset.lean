import LeanCompCert.Ports.PsiRuntimePrimeTable

/-!
# Compiled reset of the runtime psi prime-power table

Consecutive source-scale psi shards reuse one shared array.  Their resident
prime table and carry cells must survive, but the shard-local prime-power
table must start with zero padding before it is regenerated.  The total
cursor also reads one permanent pair at rank `ppCount`, so the reset includes
that `(0,0)` sentinel rather than inheriting an unproved caller-memory fact.
This small compiled stage clears exactly those `ppCount + 1` pairs.  It
contains no table literals and its loop count is only that scalar bound.
-/

set_option autoImplicit false

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve

def psiPPResetBody (m : PsiRuntimeMeta) : List AInstr :=
  [ .scalar (.binop 10 .shl .idx (.lit 1))
  , .scalar (.binop 11 .add (.reg 10) (.lit m.cfg.ppBase))
  , .store 11 rZero
  , .scalar (.binop 12 .add (.reg 11) (.lit 1))
  , .store 12 rZero ]

def psiPPResetProgram (m : PsiRuntimeMeta) : AProgram :=
  { regCount := regCount
    arrayLen := m.arrayLen
    loopCount := m.ppCount + 1
    init := seedRegs [(rZero, 0)]
    body := psiPPResetBody m
    epilogue := []
    output := rZero }

theorem psiPPResetBody_all (m : PsiRuntimeMeta) :
    (psiPPResetBody m).all (ainstrWFB regCount) = true := by
  rfl

theorem psiPPResetProgram_wf (m : PsiRuntimeMeta) :
    (psiPPResetProgram m).WF := by
  unfold psiPPResetProgram
  refine ⟨show rZero < regCount by decide,
    forall_wf_of_all (by rfl),
    forall_wf_of_all (psiPPResetBody_all m), ?_⟩
  intro a h
  cases h

theorem psiPPResetProgram_compiled (m : PsiRuntimeMeta) (base : Int)
    (hBase : BaseOk (psiPPResetProgram m).arrayLen base)
    (n : Nat) (hDenote : (psiPPResetProgram m).denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          ((psiPPResetProgram m).initialMCC base)
          (psiPPResetProgram m).compile)
        (fun st : Verified.MemFragment.MCCState =>
          st.env ⟨(psiPPResetProgram m).output + 1⟩) =
      some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ (psiPPResetProgram_wf m) base hBase n hDenote

#print axioms psiPPResetProgram_wf
#print axioms psiPPResetProgram_compiled

end LeanCompCert.Ports.PsiSegSieve

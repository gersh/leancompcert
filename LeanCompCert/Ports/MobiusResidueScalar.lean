import LeanCompCert.Ports.MobiusResidueRealisation
import LeanCompCert.Verified.ScalarLift

/-!
# The live Möbius residue as a scalar block

`ArraySegSieve.mobiusLiveResidue` contains no load or store: its fifty
instructions are all `.scalar`.  The segmented sieve uses the array wrapper,
but the already verified `MertensCDEM` trial-division core is a scalar
`Reflect.Program`.  This file removes that representational mismatch once.

The scalar block below is not a second transcription.  It is obtained by
forgetting the `.scalar` constructor, and `residue_map_scalar` proves that
lifting it recreates the original block exactly.  Consequently
`residue_denote` is a direct corollary of
`MobiusResidueRealisation.mobiusLiveResidue_denote`; no instruction is
reproved and no computation is admitted.
-/

namespace LeanCompCert.Ports.MobiusResidueScalar

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.MobiusResidueRealisation

/-- Forget the array wrapper.  The non-scalar cases are unreachable for the
live residue; choosing a total fallback keeps the extraction definition
ordinary data rather than an `Option`-valued partial pass. -/
def scalarOf : AInstr → Instr
  | .scalar i => i
  | .load _ _ => .mov 0 (.lit 0)
  | .store _ _ => .mov 0 (.lit 0)

/-- The exact fifty-instruction live residue in the scalar fragment. -/
def residue (k : Nat) : List Instr :=
  (mobiusLiveResidue k).map scalarOf

/-- Lifting the extracted block gives the source array block exactly. -/
theorem residue_map_scalar (k : Nat) :
    (residue k).map AInstr.scalar = mobiusLiveResidue k := by
  rfl

/-- The four input signals read from a scalar register file. -/
def readSig (s : RegState) : Sig :=
  ⟨s 65, s 79, s 80, s 133⟩

/-- The five persistent residue fields read from a scalar register file. -/
def readRes (s : RegState) : Res :=
  ⟨s rTLo, s rTHi, s rCeil, s rCeilSq, s rMViol⟩

/-- The transparent name of the residue's updated-ceiling divisor, exposed
without making clients unfold either structured register read. -/
theorem celAfter_read (s : RegState) :
    celAfter (readSig s) (readRes s) =
      (celStep (s 65) (s 103) (s 102) (s 133)).1 := rfl

theorem readSig_liftState (s : RegState) :
    MobiusResidueRealisation.readSig (liftState s) = readSig s := rfl

theorem readRes_liftState (s : RegState) :
    MobiusResidueRealisation.readRes (liftState s) = readRes s := rfl

/--
**Scalar denotation of the complete residue.**  The hypotheses are precisely
the two nonzero divisors of the block.  Successful scalar execution advances
the five-field transparent model by `resStep`, exactly as the array-wrapped
block does.
-/
theorem residue_denote (k idx : Nat) (s s' : RegState)
    (hn : s 65 ≠ 0)
    (hc : (celStep (s 65) (s 103) (s 102) (s 133)).1 ≠ 0)
    (h : denoteInstrs idx s (residue k) = some s') :
    readRes s' = resStep k (readSig s) (readRes s) := by
  have ha : denoteAInstrs 0 idx (liftState s) (mobiusLiveResidue k) =
      some (liftState s') := by
    rw [← residue_map_scalar k,
      denoteAInstrs_map_scalar 0 idx (residue k) s, h]
    rfl
  have hm := MobiusResidueRealisation.mobiusLiveResidue_denote
    k 0 idx (liftState s) (liftState s') hn hc ha
  exact hm

/-- The scalar block is defined whenever its two mathematical divisors are
nonzero. -/
theorem residue_defined (k idx : Nat) (s : RegState)
    (hn : s 65 ≠ 0)
    (hc : (celStep (s 65) (s 103) (s 102) (s 133)).1 ≠ 0) :
    ∃ s', denoteInstrs idx s (residue k) = some s' := by
  obtain ⟨sa, ha⟩ := MobiusResidueRealisation.mobiusLiveResidue_defined
    k 0 idx (liftState s) hn hc
  cases hs : denoteInstrs idx s (residue k) with
  | none =>
      have hm := denoteAInstrs_map_scalar 0 idx (residue k) s
      rw [hs] at hm
      rw [← residue_map_scalar k, hm] at ha
      contradiction
  | some s' => exact ⟨s', rfl⟩

end LeanCompCert.Ports.MobiusResidueScalar

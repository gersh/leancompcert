import LeanCompCert.Ports.MobiusResidueScalar
import LeanCompCert.Verified.InstrBlock

/-!
# Scalar semantics for the `sum mu(n) / n` extrema residue

`ArraySegSieve.mobiusOverNResidue` is the nineteen-instruction fixed-point
accumulator used by the Helfgott `(2.11)` campaign.  It keeps the current
biased sum and its running maximum and minimum.  This file extracts that
array-wrapped scalar block without retranscription and proves its exact
machine-word transition.

The transition deliberately records the branchless selects as they execute
modulo `2^64`.  `wordMax_eq_max` and `wordMin_eq_min` then recover ordinary
`Nat.max` and `Nat.min` under the persistent word invariant.  This separation
keeps wraparound assumptions explicit for the later paper-range proof.
-/

namespace LeanCompCert.Ports.MobiusExtremaScalar

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve

/-- The exact scalar instructions obtained from the array residue. -/
def residue : List Instr :=
  mobiusOverNResidue.map MobiusResidueScalar.scalarOf

theorem residue_map_scalar :
    residue.map LeanCompCert.Verified.ArrayState.AInstr.scalar =
      mobiusOverNResidue := by
  rfl

/-- Current fixed-point sum and its unsigned running extrema. -/
structure Ext where
  t : Nat
  hi : Nat
  lo : Nat
  deriving Repr, DecidableEq

theorem Ext.eq_of {a b : Ext} (ht : a.t = b.t) (hhi : a.hi = b.hi)
    (hlo : a.lo = b.lo) : a = b := by
  cases a
  cases b
  simp_all

def readExt (s : RegState) : Ext := ⟨s rT, s rTmax, s rTmin⟩

/-- The machine's round-to-nearest weight.  The doubled remainder is itself
a word operation; a later range lemma may erase its `% M` only after proving
that the candidate is below the half-word boundary. -/
def roundWeight (n : Nat) : Nat :=
  let q := mobScale / n
  let r := mobScale % n
  q + if n ≤ (r + r) % M then 1 else 0

/-- Exact branchless maximum select, before simplifying its Boolean mask. -/
def wordMax (raw hi : Nat) : Nat :=
  let take := if hi < raw % M then 1 else 0
  (take * raw + (1 + (M - take)) * hi) % M

/-- Exact branchless minimum select, before simplifying its Boolean mask. -/
def wordMin (raw lo : Nat) : Nat :=
  let take := if raw % M < lo then 1 else 0
  (take * raw + (1 + (M - take)) * lo) % M

/-- Exact transparent transition of the nineteen scalar instructions. -/
def extStep (g : MobiusResidueRealisation.Sig) (e : Ext) : Ext :=
  let w := roundWeight g.n
  let pos := g.pos * w
  let neg := g.neg * w % M
  let raw := e.t + (pos + (M - neg))
  let t := raw % M
  ⟨t, wordMax raw e.hi, wordMin raw e.lo⟩

def ExtWord (e : Ext) : Prop := e.t < M ∧ e.hi < M ∧ e.lo < M

theorem wordMax_eq_max (raw hi : Nat) (hhi : hi < M) :
    wordMax raw hi = max (raw % M) hi := by
  unfold wordMax
  by_cases h : hi < raw % M
  · rw [if_pos h, Nat.max_eq_left (Nat.le_of_lt h)]
    simp [M]
  · rw [if_neg h, Nat.max_eq_right (Nat.le_of_not_gt h)]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero]
    change ((1 + M) * hi) % M = hi
    rw [Nat.add_mul]
    simp [Nat.mod_eq_of_lt hhi]

theorem wordMin_eq_min (raw lo : Nat) (hlo : lo < M) :
    wordMin raw lo = min (raw % M) lo := by
  unfold wordMin
  by_cases h : raw % M < lo
  · rw [if_pos h, Nat.min_eq_left (Nat.le_of_lt h)]
    simp [M]
  · rw [if_neg h, Nat.min_eq_right (Nat.le_of_not_gt h)]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero]
    change ((1 + M) * lo) % M = lo
    rw [Nat.add_mul]
    simp [Nat.mod_eq_of_lt hlo]

/-- Every exact transition produces three machine words. -/
theorem extStep_word (g : MobiusResidueRealisation.Sig) (e : Ext) :
    ExtWord (extStep g e) := by
  unfold ExtWord extStep wordMax wordMin
  dsimp only
  exact ⟨Nat.mod_lt _ M_pos, Nat.mod_lt _ M_pos, Nat.mod_lt _ M_pos⟩

/-- Total execution has exactly the transparent transition above. -/
theorem readExt_srun (idx : Nat) (s : RegState) (hn : s 65 ≠ 0) :
    readExt (srun idx s residue) =
      extStep (MobiusResidueScalar.readSig s) (readExt s) := by
  apply Ext.eq_of <;>
  simp [residue, MobiusResidueScalar.scalarOf, mobiusOverNResidue,
    srun, sdest, sval, denoteOperand, denoteOp, RegState.set,
    MobiusResidueScalar.readSig, extStep, roundWeight, wordMax, wordMin,
    Option.getD_some, hn, rT, rTmax, rTmin, mobScale, M] <;> rfl

/-- The only partial operations are division and remainder by the nonzero
candidate in register 65. -/
theorem residue_defined (idx : Nat) (s : RegState) (hn : s 65 ≠ 0) :
    denoteInstrs idx s residue = some (srun idx s residue) := by
  apply denoteInstrs_eq_srun
  simp [residue, MobiusResidueScalar.scalarOf, mobiusOverNResidue,
    SAllDefined, SDefined, sdest, sval, denoteOperand, denoteOp,
    RegState.set, hn]

/-- Successful instruction denotation refines to the exact extrema step. -/
theorem residue_denote (idx : Nat) (s s' : RegState) (hn : s 65 ≠ 0)
    (h : denoteInstrs idx s residue = some s') :
    readExt s' = extStep (MobiusResidueScalar.readSig s) (readExt s) := by
  rw [residue_defined idx s hn] at h
  cases h
  exact readExt_srun idx s hn

end LeanCompCert.Ports.MobiusExtremaScalar

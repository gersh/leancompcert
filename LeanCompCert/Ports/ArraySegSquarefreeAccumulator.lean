import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.RegFrame

/-!
# Exact squarefree-count accumulator in the live segmented residue

This isolates instructions 3--7 of `mertensLiveResidue`: the squarefree count
`Q` and biased fixed-point discrepancy `G`.  The proof is symbolic in the
incoming words and does not execute a sieve or a production range.
-/

namespace LeanCompCert.Ports.ArraySegSquarefreeAccumulator

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Ports.ArraySegSieve

/-- The literal `Q,G` prefix after the two Mertens-update instructions. -/
def qgBlock : List Instr :=
  [ .binop rQ .add (.reg rQ) (.reg 81)
  , .binop 113 .shl (.reg 81) (.lit cdemScale)
  , .binop 114 .mul (.reg 133) (.lit cdemC)
  , .binop 115 .add (.reg rG) (.reg 113)
  , .binop rG .sub (.reg 115) (.reg 114) ]

/-- This block is obtained from the actual emitted residue, not a parallel
reimplementation. -/
theorem live_qg_slice_eq (bNum bDen : Nat) :
    ((mertensLiveResidue bNum bDen).drop 2).take 5 =
      qgBlock.map LeanCompCert.Verified.ArrayState.AInstr.scalar := by
  rfl

def qStage : List Instr :=
  [ .binop rQ .add (.reg rQ) (.reg 81) ]

def deltaStage : List Instr :=
  [ .binop 113 .shl (.reg 81) (.lit cdemScale)
  , .binop 114 .mul (.reg 133) (.lit cdemC) ]

def commitStage : List Instr :=
  [ .binop 115 .add (.reg rG) (.reg 113)
  , .binop rG .sub (.reg 115) (.reg 114) ]

theorem qgBlock_eq_stages :
    qgBlock = qStage ++ deltaStage ++ commitStage := by rfl

def qNext (q squarefree : Nat) : Nat := (q + squarefree) % M

def shiftedSquarefree (squarefree : Nat) : Nat :=
  (squarefree <<< (cdemScale % M)) % M

def coefficientStep (gate coeffWord : Nat) : Nat :=
  (gate * coeffWord) % M

def gNext (g squarefree gate coeffWord : Nat) : Nat :=
  ((g + shiftedSquarefree squarefree) % M +
    (M - coefficientStep gate coeffWord)) % M

private theorem one_binop_run (idx : Nat) (s : RegState)
    (dest : Nat) (op : Op) (lhs rhs : Operand) :
    (srun idx s [.binop dest op lhs rhs]) dest =
      (denoteOp op (denoteOperand idx s lhs)
        (denoteOperand idx s rhs)).getD 0 := by
  let i : Instr := .binop dest op lhs rhs
  exact (srun_read_head idx dest i [] (by rfl) (by rfl) s).trans rfl

private theorem one_binop_frame (idx : Nat) (s : RegState)
    (dest keep : Nat) (op : Op) (lhs rhs : Operand) (h : dest ≠ keep) :
    (srun idx s [.binop dest op lhs rhs]) keep = s keep := by
  apply srun_untouched
  intro i hi
  simp only [List.mem_singleton] at hi
  subst i
  simpa only [sdest] using h

private theorem qStage_run (idx : Nat) (s : RegState) (q squarefree : Nat)
    (hq : s rQ = q) (hsq : s 81 = squarefree) :
    (srun idx s qStage) rQ = qNext q squarefree := by
  have h := one_binop_run idx s rQ .add (.reg rQ) (.reg 81)
  simpa only [qStage, qNext, denoteOp, denoteOperand, Option.getD_some,
    hq, hsq] using h

private theorem shiftStage_run (idx : Nat) (s : RegState)
    (squarefree : Nat) (hsq : s 81 = squarefree) :
    (srun idx s [.binop 113 .shl (.reg 81) (.lit cdemScale)]) 113 =
      shiftedSquarefree squarefree := by
  have h0 :
      (srun idx s [.binop 113 .shl (.reg 81) (.lit cdemScale)]) 113 =
        (s 81 <<< (cdemScale % M)) % M :=
    one_binop_run idx s 113 .shl (.reg 81) (.lit cdemScale)
  exact h0.trans (by rw [hsq]; rfl)

private theorem coefficientStage_run (idx : Nat) (s : RegState)
    (gate coeff : Nat) (hgate : s 133 = gate) :
    (srun idx s [.binop 114 .mul (.reg 133) (.lit coeff)]) 114 =
      coefficientStep gate (coeff % M) := by
  have h0 :
      (srun idx s [.binop 114 .mul (.reg 133) (.lit coeff)]) 114 =
        (s 133 * (coeff % M)) % M :=
    one_binop_run idx s 114 .mul (.reg 133) (.lit coeff)
  exact h0.trans (by rw [hgate]; rfl)

private theorem deltaStage_run (idx : Nat) (s : RegState)
    (squarefree gate : Nat) (hsq : s 81 = squarefree)
    (hgate : s 133 = gate) :
    (srun idx s deltaStage) 113 = shiftedSquarefree squarefree ∧
      (srun idx s deltaStage) 114 = coefficientStep gate (cdemC % M) := by
  let s1 := srun idx s
    [.binop 113 .shl (.reg 81) (.lit cdemScale)]
  have hshift0 : s1 113 =
      (s 81 <<< (cdemScale % M)) % M :=
    one_binop_run idx s 113 .shl (.reg 81) (.lit cdemScale)
  have hshift : s1 113 = shiftedSquarefree squarefree := by
    exact hshift0.trans (by rw [hsq]; rfl)
  have hs1Gate : s1 133 = gate :=
    (one_binop_frame idx s 113 133 .shl (.reg 81) (.lit cdemScale)
      (by omega)).trans hgate
  have hcoef :
      (srun idx s1 [.binop 114 .mul (.reg 133) (.lit cdemC)]) 114 =
        coefficientStep gate (cdemC % M) := by
    exact coefficientStage_run idx s1 gate cdemC hs1Gate
  have hshiftFrame :
      (srun idx s1 [.binop 114 .mul (.reg 133) (.lit cdemC)]) 113 =
        shiftedSquarefree squarefree :=
    (one_binop_frame idx s1 114 113 .mul (.reg 133) (.lit cdemC)
      (by omega)).trans hshift
  rw [show deltaStage =
    [.binop 113 .shl (.reg 81) (.lit cdemScale)] ++
      [.binop 114 .mul (.reg 133) (.lit cdemC)] by rfl,
    srun_append]
  exact ⟨hshiftFrame, hcoef⟩

private theorem commitStage_run (idx : Nat) (s : RegState)
    (g shift coeff : Nat) (hg : s rG = g) (hshift : s 113 = shift)
    (hcoeff : s 114 = coeff) :
    (srun idx s commitStage) rG =
      ((g + shift) % M + (M - coeff)) % M := by
  let s1 := srun idx s [.binop 115 .add (.reg rG) (.reg 113)]
  have hadd0 := one_binop_run idx s 115 .add (.reg rG) (.reg 113)
  have hadd : s1 115 = (g + shift) % M := by
    simpa only [s1, denoteOp, denoteOperand, Option.getD_some, hg, hshift]
      using hadd0
  have hs1Coeff : s1 114 = coeff :=
    (one_binop_frame idx s 115 114 .add (.reg rG) (.reg 113)
      (by omega)).trans hcoeff
  have hsub0 := one_binop_run idx s1 rG .sub (.reg 115) (.reg 114)
  have hsub :
      (srun idx s1 [.binop rG .sub (.reg 115) (.reg 114)]) rG =
        ((g + shift) % M + (M - coeff)) % M := by
    simpa only [denoteOp, denoteOperand, Option.getD_some, hadd, hs1Coeff]
      using hsub0
  rw [show commitStage =
    [.binop 115 .add (.reg rG) (.reg 113)] ++
      [.binop rG .sub (.reg 115) (.reg 114)] by rfl,
    srun_append]
  exact hsub

/-- Exact machine-word semantics of the five actual emitted instructions. -/
theorem qgBlock_run (idx : Nat) (s : RegState)
    (q squarefree g gate : Nat) (hq : s rQ = q) (hsq : s 81 = squarefree)
    (hg : s rG = g) (hgate : s 133 = gate) :
      (srun idx s qgBlock) rQ = qNext q squarefree ∧
      (srun idx s qgBlock) rG = gNext g squarefree gate (cdemC % M) := by
  let s1 := srun idx s qStage
  let s2 := srun idx s1 deltaStage
  have hq1 := qStage_run idx s q squarefree hq hsq
  have hs1Sq : s1 81 = squarefree :=
    (srun_untouched idx 81 qStage (by decide) s).trans hsq
  have hs1Gate : s1 133 = gate :=
    (srun_untouched idx 133 qStage (by decide) s).trans hgate
  have hs1G : s1 rG = g :=
    (srun_untouched idx rG qStage (by decide) s).trans hg
  have hd := deltaStage_run idx s1 squarefree gate hs1Sq hs1Gate
  have hs2G : s2 rG = g :=
    (srun_untouched idx rG deltaStage (by decide) s1).trans hs1G
  have hg2 := commitStage_run idx s2 g
    (shiftedSquarefree squarefree) (coefficientStep gate (cdemC % M))
      hs2G hd.1 hd.2
  have hq2 : (srun idx s2 commitStage) rQ = qNext q squarefree :=
    (srun_untouched idx rQ commitStage (by decide) s2).trans
      ((srun_untouched idx rQ deltaStage (by decide) s1).trans hq1)
  rw [qgBlock_eq_stages, srun_append, srun_append]
  exact ⟨hq2, hg2⟩

/-- In the main phase, ordinary no-wrap bounds turn the machine transition
into the mathematical `Q,G` recurrence. -/
theorem qgBlock_run_main_nowrap (idx : Nat) (s : RegState)
    (q squarefree g : Nat) (hq : s rQ = q) (hsq : s 81 = squarefree)
    (hg : s rG = g) (hgate : s 133 = 1)
    (hqM : q + squarefree < M)
    (hshiftM : squarefree * 2 ^ cdemScale < M)
    (hcoeffLe : cdemC ≤ g + squarefree * 2 ^ cdemScale)
    (hgM : g + squarefree * 2 ^ cdemScale < M) :
    (srun idx s qgBlock) rQ = q + squarefree ∧
      (srun idx s qgBlock) rG =
        g + squarefree * 2 ^ cdemScale - cdemC := by
  have hrun := qgBlock_run idx s q squarefree g 1 hq hsq hg hgate
  have hscale : cdemScale % M = cdemScale :=
    Nat.mod_eq_of_lt (by decide)
  have hc : cdemC % M = cdemC :=
    Nat.mod_eq_of_lt (by decide)
  have hshift : shiftedSquarefree squarefree =
      squarefree * 2 ^ cdemScale := by
    simp only [shiftedSquarefree, hscale, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt hshiftM
  have hcoef : coefficientStep 1 (cdemC % M) = cdemC := by
    simp only [coefficientStep, hc, Nat.one_mul]
  have hsub :
      (g + squarefree * 2 ^ cdemScale + (M - cdemC)) % M =
        g + squarefree * 2 ^ cdemScale - cdemC := by
    rw [show g + squarefree * 2 ^ cdemScale + (M - cdemC) =
        M + (g + squarefree * 2 ^ cdemScale - cdemC) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [qNext, Nat.mod_eq_of_lt hqM, gNext, hshift, hcoef,
    Nat.mod_eq_of_lt hgM, hsub] at hrun
  exact hrun

#print axioms live_qg_slice_eq
#print axioms qgBlock_run
#print axioms qgBlock_run_main_nowrap

end LeanCompCert.Ports.ArraySegSquarefreeAccumulator

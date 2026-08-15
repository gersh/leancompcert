import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.RegFrame

/-!
# Exact semantics of the Hurst comparison in the segmented Möbius program

This isolates the six literal instructions in `mertensLiveResidue` which test
the two sides of Hurst's `|M(n)| ≤ 0.571 √n` bound.  The split theorem below
shows that this is the block actually emitted by the production program; the
subsequent theorems give its exact machine-word semantics.
-/

namespace LeanCompCert.Ports.ArraySegMertensHurstCheck

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Ports.ArraySegSieve

/-- The literal Hurst comparison, extracted without changing the production
instruction stream. -/
def checkBlock : List Instr :=
  [ .binop 154 .mul (.reg rS) (.lit hurstA)
  , .binop 155 .lshr (.reg 154) (.lit 32)
  , .binop 156 .add (.lit mertensBias) (.reg 155)
  , .binop 157 .sub (.lit mertensBias) (.reg 155)
  , .binop 158 .gt (.reg rM) (.reg 156)
  , .binop 159 .lt (.reg rM) (.reg 157) ]

/-- This scalar block is exactly the named block emitted by the actual live
Mertens/squarefree program. -/
theorem liveBlock_eq : hurstLiveCheckBlock =
    checkBlock.map LeanCompCert.Verified.ArrayState.AInstr.scalar := by
  simp [hurstLiveCheckBlock, checkBlock]

/-- Exact machine-word threshold produced by the multiply-and-shift prefix. -/
def threshold (sqrtN : Nat) : Nat :=
  (((sqrtN * (hurstA % M)) % M) >>> (32 % M)) % M

def scaleMul : Instr := .binop 154 .mul (.reg rS) (.lit hurstA)
def scaleShift : Instr := .binop 155 .lshr (.reg 154) (.lit 32)
def scaleStage : List Instr := [scaleMul, scaleShift]

def intervalStage : List Instr :=
  [ .binop 156 .add (.lit mertensBias) (.reg 155)
  , .binop 157 .sub (.lit mertensBias) (.reg 155) ]

def flagStage : List Instr :=
  [ .binop 158 .gt (.reg rM) (.reg 156)
  , .binop 159 .lt (.reg rM) (.reg 157) ]

theorem checkBlock_eq_stages :
    checkBlock = scaleStage ++ intervalStage ++ flagStage := by rfl

private theorem two_mul_shift_run (idx : Nat) (s : RegState)
    (mulDest shiftDest source literal amount : Nat) :
    (srun idx s
      [ .binop mulDest .mul (.reg source) (.lit literal)
      , .binop shiftDest .lshr (.reg mulDest) (.lit amount) ]) shiftDest =
      (((s source * (literal % M)) % M) >>> (amount % M)) % M := by
  let mulI : Instr := .binop mulDest .mul (.reg source) (.lit literal)
  let shiftI : Instr := .binop shiftDest .lshr (.reg mulDest) (.lit amount)
  have hmul : (srun idx s [mulI]) mulDest =
      (s source * (literal % M)) % M := by
    exact (srun_read_head idx mulDest mulI [] (by rfl) (by rfl) s).trans rfl
  calc
    (srun idx s [mulI, shiftI]) shiftDest =
        sval idx (srun idx s [mulI]) shiftI := by
      rw [show [mulI, shiftI] = [mulI] ++ [shiftI] by rfl]
      exact srun_read_last idx shiftDest [mulI] shiftI (by rfl) s
    _ = (((srun idx s [mulI]) mulDest >>> (amount % M)) % M) := rfl
    _ = (((s source * (literal % M)) % M) >>> (amount % M)) % M :=
      congrArg (fun x => (x >>> (amount % M)) % M) hmul

private theorem scaleStage_run (idx : Nat) (s : RegState) (sqrtN : Nat)
    (hsqrt : s rS = sqrtN) :
    (srun idx s scaleStage) 155 =
      (((sqrtN * (hurstA % M)) % M) >>> (32 % M)) % M := by
  have h := two_mul_shift_run idx s 154 155 rS hurstA 32
  have hs := congrArg
    (fun x => (((x * (hurstA % M)) % M) >>> (32 % M)) % M) hsqrt
  have h' : (srun idx s scaleStage) 155 =
      (((s rS * (hurstA % M)) % M) >>> (32 % M)) % M := by
    simpa only [scaleStage, scaleMul, scaleShift] using h
  exact h'.trans hs

private theorem intervalStage_run (idx : Nat) (s : RegState) (t : Nat)
    (htReg : s 155 = t) (ht : t ≤ mertensBias)
    (hhi : mertensBias + t < M) :
    (srun idx s intervalStage) 156 = mertensBias + t ∧
      (srun idx s intervalStage) 157 = mertensBias - t := by
  have hbias : mertensBias % M = mertensBias := by decide
  have hsub : (mertensBias + (M - t)) % M = mertensBias - t := by
    have heq : mertensBias + (M - t) = M + (mertensBias - t) := by omega
    have hdiff : mertensBias - t < M := by
      have hbiasLt : mertensBias < M := by decide
      omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add]
    rw [Nat.mod_eq_of_lt hdiff]
    exact Nat.mod_eq_of_lt hdiff
  simp [intervalStage, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, htReg, hbias, Nat.mod_eq_of_lt hhi, hsub]

private theorem flagStage_run (idx : Nat) (s : RegState)
    (m lo hi : Nat) (hm : s rM = m) (hlo : s 157 = lo)
    (hhi : s 156 = hi) :
    (srun idx s flagStage) 158 = (if m > hi then 1 else 0) ∧
      (srun idx s flagStage) 159 = (if m < lo then 1 else 0) := by
  have hm' : s 100 = m := by simpa [rM] using hm
  simp [flagStage, srun, RegState.set, sdest, sval,
    denoteOperand, denoteOp, rM, hm', hlo, hhi]

/-- Exact semantics of the actual six emitted Hurst instructions. -/
theorem checkBlock_run (idx : Nat) (s : RegState) (sqrtN m : Nat)
    (hsqrt : s rS = sqrtN) (hm : s rM = m)
    (ht : threshold sqrtN ≤ mertensBias)
    (hhi : mertensBias + threshold sqrtN < M) :
    (srun idx s checkBlock) 158 =
        (if m > mertensBias + threshold sqrtN then 1 else 0) ∧
      (srun idx s checkBlock) 159 =
        (if m < mertensBias - threshold sqrtN then 1 else 0) := by
  let s1 := srun idx s scaleStage
  let s2 := srun idx s1 intervalStage
  have hs1 := scaleStage_run idx s sqrtN hsqrt
  have hs1m : s1 rM = m := by
    exact (srun_untouched idx rM scaleStage (by decide) s).trans hm
  have hs2 := intervalStage_run idx s1 (threshold sqrtN) hs1 ht hhi
  have hs2m : s2 rM = m := by
    exact (srun_untouched idx rM intervalStage (by decide) s1).trans hs1m
  rw [checkBlock_eq_stages, srun_append, srun_append]
  exact flagStage_run idx s2 m _ _ hs2m hs2.2 hs2.1

/-- Zero flags imply the intended ordinary biased interval. -/
theorem bounds_of_flags_zero (idx : Nat) (s : RegState) (sqrtN m : Nat)
    (hsqrt : s rS = sqrtN) (hm : s rM = m)
    (ht : threshold sqrtN ≤ mertensBias)
    (hhi : mertensBias + threshold sqrtN < M)
    (hupper : (srun idx s checkBlock) 158 = 0)
    (hlower : (srun idx s checkBlock) 159 = 0) :
    mertensBias - threshold sqrtN ≤ m ∧
      m ≤ mertensBias + threshold sqrtN := by
  have hrun := checkBlock_run idx s sqrtN m hsqrt hm ht hhi
  rw [hupper, hlower] at hrun
  by_cases hu : m > mertensBias + threshold sqrtN
  · simp [hu] at hrun
  by_cases hl : m < mertensBias - threshold sqrtN
  · simp [hl] at hrun
  exact ⟨Nat.le_of_not_gt hl, Nat.le_of_not_gt hu⟩

/-- The exact machine threshold is no larger than the intended dyadic
product.  This lemma deliberately remains valid even if the multiplication
wrapped: every `% M` can only make the threshold smaller. -/
theorem threshold_mul_scale_le (sqrtN : Nat) :
    threshold sqrtN * 2 ^ 32 ≤ sqrtN * hurstA := by
  have h32 : 32 % M = 32 := by decide
  unfold threshold
  rw [h32, Nat.shiftRight_eq_div_pow]
  let raw := (sqrtN * (hurstA % M)) % M
  calc
    (raw / 2 ^ 32 % M) * 2 ^ 32 ≤ (raw / 2 ^ 32) * 2 ^ 32 :=
      Nat.mul_le_mul_right _ (Nat.mod_le _ _)
    _ ≤ raw := Nat.div_mul_le_self _ _
    _ ≤ sqrtN * (hurstA % M) := Nat.mod_le _ _
    _ ≤ sqrtN * hurstA :=
      Nat.mul_le_mul_left _ (Nat.mod_le _ _)

#print axioms checkBlock_run
#print axioms bounds_of_flags_zero
#print axioms threshold_mul_scale_le

end LeanCompCert.Ports.ArraySegMertensHurstCheck

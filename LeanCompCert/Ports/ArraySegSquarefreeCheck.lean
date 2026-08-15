import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Verified.InstrBlock
import LeanCompCert.Verified.RegFrame

/-!
# Exact semantics of the CDEM squarefree comparison

This isolates the six literal instructions in `mertensLiveResidue` which test
the two sides of the Cohen--Dress--El Marraki squarefree-count bound.  No
production sweep is evaluated here; the theorem is symbolic in all live
machine words.
-/

namespace LeanCompCert.Ports.ArraySegSquarefreeCheck

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Ports.ArraySegSieve

def checkBlock (bNum bDen : Nat) : List Instr :=
  [ .binop 160 .mul (.reg rS) (.lit (cdemB bNum bDen))
  , .binop 161 .add (.lit gBias) (.reg 160)
  , .binop 162 .add (.lit (gBias + cdemC + 1)) (.reg 65)
  , .binop 163 .sub (.reg 162) (.reg 160)
  , .binop 164 .gt (.reg rG) (.reg 161)
  , .binop 165 .lt (.reg rG) (.reg 163) ]

theorem liveBlock_eq (bNum bDen : Nat) :
    squarefreeLiveCheckBlock bNum bDen =
      (checkBlock bNum bDen).map
        LeanCompCert.Verified.ArrayState.AInstr.scalar := by
  simp [squarefreeLiveCheckBlock, checkBlock]

def threshold (bNum bDen sqrtN : Nat) : Nat :=
  (sqrtN * (cdemB bNum bDen % M)) % M

def thresholdStage (bNum bDen : Nat) : List Instr :=
  [ .binop 160 .mul (.reg rS) (.lit (cdemB bNum bDen)) ]

def intervalUpperStage : List Instr :=
  [ .binop 161 .add (.lit gBias) (.reg 160) ]

def intervalBaseStage : List Instr :=
  [ .binop 162 .add (.lit (gBias + cdemC + 1)) (.reg 65) ]

def intervalLowerStage : List Instr :=
  [ .binop 163 .sub (.reg 162) (.reg 160) ]

def intervalStage : List Instr :=
  intervalUpperStage ++ intervalBaseStage ++ intervalLowerStage

def flagStage : List Instr :=
  [ .binop 164 .gt (.reg rG) (.reg 161)
  , .binop 165 .lt (.reg rG) (.reg 163) ]

theorem checkBlock_eq_stages (bNum bDen : Nat) :
    checkBlock bNum bDen =
      thresholdStage bNum bDen ++ intervalStage ++ flagStage := by rfl

private theorem one_mul_run (idx : Nat) (s : RegState)
    (dest source literal : Nat) :
    (srun idx s [.binop dest .mul (.reg source) (.lit literal)]) dest =
      (s source * (literal % M)) % M := by
  let mulI : Instr := .binop dest .mul (.reg source) (.lit literal)
  exact (srun_read_head idx dest mulI [] (by rfl) (by rfl) s).trans rfl

private theorem thresholdStage_run (bNum bDen idx : Nat) (s : RegState)
    (sqrtN : Nat) (hsqrt : s rS = sqrtN) :
    (srun idx s (thresholdStage bNum bDen)) 160 =
      threshold bNum bDen sqrtN := by
  have h := one_mul_run idx s 160 rS (cdemB bNum bDen)
  have hs := congrArg
    (fun x => (x * (cdemB bNum bDen % M)) % M) hsqrt
  have h' : (srun idx s (thresholdStage bNum bDen)) 160 =
      (s rS * (cdemB bNum bDen % M)) % M := by
    simpa only [thresholdStage] using h
  exact h'.trans hs

private theorem intervalUpperStage_run (idx : Nat) (s : RegState)
    (t : Nat) (ht : s 160 = t) (hupper : gBias + t < M) :
    (srun idx s intervalUpperStage) 161 = gBias + t := by
  have hg : gBias % M = gBias := by decide
  change (gBias % M + s 160) % M = _
  rw [ht, hg, Nat.mod_eq_of_lt hupper]

private theorem intervalBaseStage_run (idx : Nat) (s : RegState)
    (n : Nat) (hn : s 65 = n)
    (hbase : gBias + cdemC + 1 + n < M) :
    (srun idx s intervalBaseStage) 162 = gBias + cdemC + 1 + n := by
  have hbaseLit : (gBias + cdemC + 1) % M = gBias + cdemC + 1 := by
    apply Nat.mod_eq_of_lt
    omega
  change ((gBias + cdemC + 1) % M + s 65) % M = _
  rw [hn, hbaseLit, Nat.mod_eq_of_lt hbase]

private theorem intervalLowerStage_run (idx : Nat) (s : RegState)
    (base t : Nat) (hbaseReg : s 162 = base) (htReg : s 160 = t)
    (hbase : base < M) (htle : t ≤ base) :
    (srun idx s intervalLowerStage) 163 = base - t := by
  have hsub : (base + (M - t)) % M = base - t := by
    have htM : t < M := by omega
    rw [show base + (M - t) = M + (base - t) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  change (s 162 + (M - s 160)) % M = _
  rw [hbaseReg, htReg, hsub]

private theorem intervalStage_run (idx : Nat) (s : RegState)
    (n t : Nat) (hn : s 65 = n) (ht : s 160 = t)
    (hupper : gBias + t < M)
    (hbase : gBias + cdemC + 1 + n < M)
    (htle : t ≤ gBias + cdemC + 1 + n) :
    (srun idx s intervalStage) 161 = gBias + t ∧
      (srun idx s intervalStage) 163 =
        gBias + cdemC + 1 + n - t := by
  let su := srun idx s intervalUpperStage
  let sb := srun idx su intervalBaseStage
  have hu := intervalUpperStage_run idx s t ht hupper
  have suN : su 65 = n :=
    (srun_untouched idx 65 intervalUpperStage (by decide) s).trans hn
  have suT : su 160 = t :=
    (srun_untouched idx 160 intervalUpperStage (by decide) s).trans ht
  have hb := intervalBaseStage_run idx su n suN hbase
  have sbT : sb 160 = t :=
    (srun_untouched idx 160 intervalBaseStage (by decide) su).trans suT
  have sbU : sb 161 = gBias + t :=
    (srun_untouched idx 161 intervalBaseStage (by decide) su).trans hu
  have hl := intervalLowerStage_run idx sb (gBias + cdemC + 1 + n) t
    hb sbT hbase htle
  have slU : (srun idx sb intervalLowerStage) 161 = gBias + t :=
    (srun_untouched idx 161 intervalLowerStage (by decide) sb).trans sbU
  rw [intervalStage, srun_append, srun_append]
  exact ⟨slU, hl⟩

private theorem flagStage_run (idx : Nat) (s : RegState)
    (g lo hi : Nat) (hg : s rG = g) (hlo : s 163 = lo)
    (hhi : s 161 = hi) :
    (srun idx s flagStage) 164 = (if g > hi then 1 else 0) ∧
      (srun idx s flagStage) 165 = (if g < lo then 1 else 0) := by
  have hg' : s 116 = g := by simpa only [rG] using hg
  simp [flagStage, srun, RegState.set, sdest, sval, denoteOperand,
    denoteOp, rG, hg', hlo, hhi]

/-- Exact machine-word semantics of the actual emitted comparison. -/
theorem checkBlock_run (bNum bDen idx : Nat) (s : RegState)
    (n sqrtN g : Nat) (hn : s 65 = n) (hsqrt : s rS = sqrtN)
    (hg : s rG = g)
    (hupper : gBias + threshold bNum bDen sqrtN < M)
    (hbase : gBias + cdemC + 1 + n < M)
    (htle : threshold bNum bDen sqrtN ≤ gBias + cdemC + 1 + n) :
    (srun idx s (checkBlock bNum bDen)) 164 =
        (if g > gBias + threshold bNum bDen sqrtN then 1 else 0) ∧
      (srun idx s (checkBlock bNum bDen)) 165 =
        (if g < gBias + cdemC + 1 + n -
          threshold bNum bDen sqrtN then 1 else 0) := by
  let s1 := srun idx s (thresholdStage bNum bDen)
  let s2 := srun idx s1 intervalStage
  have hs1 := thresholdStage_run bNum bDen idx s sqrtN hsqrt
  have h65 : ∀ i ∈ thresholdStage bNum bDen, sdest i ≠ 65 := by
    intro i hi
    simp only [thresholdStage, List.mem_singleton] at hi
    subst i
    simp only [sdest]
    omega
  have hG : ∀ i ∈ thresholdStage bNum bDen, sdest i ≠ rG := by
    intro i hi
    simp only [thresholdStage, List.mem_singleton] at hi
    subst i
    simp only [sdest, rG]
    omega
  have hs1n : s1 65 = n :=
    (srun_untouched idx 65 (thresholdStage bNum bDen) h65 s).trans hn
  have hs1g : s1 rG = g :=
    (srun_untouched idx rG (thresholdStage bNum bDen) hG s).trans hg
  have hs2 := intervalStage_run idx s1 n (threshold bNum bDen sqrtN)
    hs1n hs1 hupper hbase htle
  have hs2g : s2 rG = g :=
    (srun_untouched idx rG intervalStage (by decide) s1).trans hs1g
  rw [checkBlock_eq_stages, srun_append, srun_append]
  exact flagStage_run idx s2 g _ _ hs2g hs2.2 hs2.1

/-- Zero flags imply the ordinary biased interval tested by the program. -/
theorem bounds_of_flags_zero (bNum bDen idx : Nat) (s : RegState)
    (n sqrtN g : Nat) (hn : s 65 = n) (hsqrt : s rS = sqrtN)
    (hg : s rG = g)
    (hupper : gBias + threshold bNum bDen sqrtN < M)
    (hbase : gBias + cdemC + 1 + n < M)
    (htle : threshold bNum bDen sqrtN ≤ gBias + cdemC + 1 + n)
    (hupperZero : (srun idx s (checkBlock bNum bDen)) 164 = 0)
    (hlowerZero : (srun idx s (checkBlock bNum bDen)) 165 = 0) :
    gBias + cdemC + 1 + n - threshold bNum bDen sqrtN ≤ g ∧
      g ≤ gBias + threshold bNum bDen sqrtN := by
  have hrun := checkBlock_run bNum bDen idx s n sqrtN g hn hsqrt hg
    hupper hbase htle
  rw [hupperZero, hlowerZero] at hrun
  by_cases hu : g > gBias + threshold bNum bDen sqrtN
  · simp [hu] at hrun
  by_cases hl : g < gBias + cdemC + 1 + n -
      threshold bNum bDen sqrtN
  · simp [hl] at hrun
  exact ⟨Nat.le_of_not_gt hl, Nat.le_of_not_gt hu⟩

#print axioms checkBlock_run
#print axioms bounds_of_flags_zero

end LeanCompCert.Ports.ArraySegSquarefreeCheck

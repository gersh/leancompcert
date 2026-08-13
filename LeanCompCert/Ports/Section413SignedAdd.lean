/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413SignedDiv
import LeanCompCert.Ports.Section413G1Sound

/-!
# Checked signed addition for the Section 4.1.3 scanner

This block adds two encoded signed endpoints and records ordinary two's-
complement signed overflow in a sticky violation register.  A clean compiled
run therefore proves both the mathematical sum and its signed-range guard;
wraparound is never used to justify the source recurrence.
-/

namespace LeanCompCert.Ports.Section413SignedAdd

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.Section413Cells
open LeanCompCert.Ports.Section413SignedDiv (signBit)

def rA : Nat := 280
def rB : Nat := 281
def rOut : Nat := 282
def rSignA : Nat := 283
def rSignB : Nat := 284
def rSignOut : Nat := 285
def rSame : Nat := 286
def rChanged : Nat := 287
def rBad : Nat := 288
def rViol : Nat := 289

def addStage : List Instr :=
  [.binop rOut .add (.reg rA) (.reg rB)]

def flagStage : List Instr :=
  [ .binop rSignA .ge (.reg rA) (.lit H63)
  , .binop rSignB .ge (.reg rB) (.lit H63)
  , .binop rSignOut .ge (.reg rOut) (.lit H63)
  , .binop rSame .eq (.reg rSignA) (.reg rSignB)
  , .binop rChanged .ne (.reg rSignA) (.reg rSignOut)
  , .binop rBad .mul (.reg rSame) (.reg rChanged)
  , .binop rViol .bor (.reg rViol) (.reg rBad) ]

def body : List Instr := addStage ++ flagStage

def overflowBit (a b : Nat) : Nat :=
  let out := (a + b) % M
  if signBit a = signBit b ∧ signBit a ≠ signBit out then 1 else 0

theorem body_defined (k : Nat) (s : RegState) : SAllDefined k s body :=
  sAllDefined_of_noDiv k body s (by decide)

private theorem addStage_output (k : Nat) (s : RegState) :
    srun k s addStage rOut = (s rA + s rB) % M := by
  simp [addStage, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rOut, rA, rB]

private theorem addStage_frame (k : Nat) (s : RegState) (j : Nat)
    (h : j ≠ rOut) : srun k s addStage j = s j := by
  apply srun_untouched
  intro i hi
  simp only [addStage, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl
  simpa only [sdest] using h.symm

private theorem flagStage_outputs (k : Nat) (s : RegState)
    (ha : s rA < M) (hb : s rB < M) (ho : s rOut < M)
    (hv : s rViol < M) (hout : s rOut = (s rA + s rB) % M) :
    let out := srun k s flagStage
    out rViol = s rViol ||| overflowBit (s rA) (s rB) := by
  dsimp only
  simp only [flagStage, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rSignA, rSignB, rSignOut, rSame,
    rChanged, rBad, rViol, rA, rB, rOut]
  simp only [show H63 % M = H63 by decide, Nat.reduceEqDiff, if_false,
    if_true]
  simp only [rOut, rA, rB] at hout
  rw [hout]
  unfold overflowBit signBit
  have hl0 := LeanCompCert.Ports.Section413G1Denote.lor_mod_M hv
    (show (0 : Nat) < M by exact M_pos)
  have hl1 := LeanCompCert.Ports.Section413G1Denote.lor_mod_M hv
    (show (1 : Nat) < M by decide)
  simp only [rViol] at hv hl0 hl1
  by_cases hsa : H63 ≤ s 280 <;> by_cases hsb : H63 ≤ s 281 <;>
    by_cases hso : H63 ≤ (s 280 + s 281) % M <;>
    simp [hsa, hsb, hso, Nat.mod_eq_of_lt hv, hl0, hl1,
      show (1 : Nat) % M = 1 by decide]

private theorem flagStage_out (k : Nat) (s : RegState) :
    srun k s flagStage rOut = s rOut := by
  apply srun_untouched
  intro i hi
  simp only [flagStage, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sdest] <;> decide

theorem body_outputs (k : Nat) (s : RegState)
    (ha : s rA < M) (hb : s rB < M) (hv : s rViol < M) :
    let out := srun k s body
    out rOut = (s rA + s rB) % M ∧
      out rViol = s rViol ||| overflowBit (s rA) (s rB) := by
  dsimp only
  let t := srun k s addStage
  have htout : t rOut = (s rA + s rB) % M := by
    simpa [t] using addStage_output k s
  have hta : t rA = s rA := by
    simpa [t] using addStage_frame k s rA (by decide)
  have htb : t rB = s rB := by
    simpa [t] using addStage_frame k s rB (by decide)
  have htv : t rViol = s rViol := by
    simpa [t] using addStage_frame k s rViol (by decide)
  have htoutM : t rOut < M := by
    rw [htout]
    exact Nat.mod_lt _ M_pos
  have hflag := flagStage_outputs k t (by simpa [hta] using ha)
    (by simpa [htb] using hb) htoutM (by simpa [htv] using hv)
    (by simpa [hta, htb] using htout)
  rw [body, srun_append]
  constructor
  · rw [flagStage_out]
    exact addStage_output k s
  · simpa [hta, htb, htv] using hflag

theorem overflowBit_zero_range (a b : Nat) (ha : a < M) (hb : b < M)
    (hz : overflowBit a b = 0) :
    -(H63 : Int) ≤ decodeZ a + decodeZ b ∧
      decodeZ a + decodeZ b < (H63 : Int) := by
  unfold overflowBit signBit at hz
  unfold decodeZ
  by_cases hsa : H63 ≤ a <;> by_cases hsb : H63 ≤ b
  · have hsumLo : M ≤ a + b := by
      simp only [M, H63] at *
      omega
    have hsumHi : a + b < 2 * M := by omega
    have hmod : (a + b) % M = a + b - M := by
      rw [Nat.mod_eq_sub_mod (by omega : M ≤ a + b)]
      rw [Nat.mod_eq_of_lt (by omega : a + b - M < M)]
    have houtSign : H63 ≤ (a + b) % M := by
      by_cases hs : H63 ≤ (a + b) % M
      · exact hs
      · have hlt : (a + b) % M < H63 := by omega
        simp [hsa, hsb, hlt] at hz
    simp only [if_neg (by omega : ¬a < H63),
      if_neg (by omega : ¬b < H63)]
    simp only [LeanCompCert.Verified.MulWide.B64, M, H63] at *
    omega
  · simp only [if_neg (by omega : ¬a < H63),
      if_pos (by omega : b < H63)]
    simp only [LeanCompCert.Verified.MulWide.B64, M, H63] at *
    omega
  · simp only [if_pos (by omega : a < H63),
      if_neg (by omega : ¬b < H63)]
    simp only [LeanCompCert.Verified.MulWide.B64, M, H63] at *
    omega
  · have hsum : a + b < M := by
      simp only [M, H63] at *
      omega
    have hmod : (a + b) % M = a + b := Nat.mod_eq_of_lt hsum
    have houtSign : (a + b) % M < H63 := by
      by_cases hs : (a + b) % M < H63
      · exact hs
      · have hge : H63 ≤ (a + b) % M := by omega
        simp [hsa, hsb, hge] at hz
    simp only [if_pos (by omega : a < H63),
      if_pos (by omega : b < H63)]
    omega

theorem clean_output_sound (k : Nat) (s : RegState)
    (ha : s rA < M) (hb : s rB < M) (hv : s rViol = 0)
    (hclean : (srun k s body) rViol = 0) :
    decodeZ ((srun k s body) rOut) = decodeZ (s rA) + decodeZ (s rB) := by
  have hout := body_outputs k s ha hb (by rw [hv]; exact M_pos)
  have hover : overflowBit (s rA) (s rB) = 0 := by
    rw [hout.2, hv] at hclean
    simpa using hclean
  have hrange := overflowBit_zero_range (s rA) (s rB) ha hb hover
  rw [hout.1]
  exact LeanCompCert.Ports.Section413G1Sound.decodeZ_add_of_range
    ha hb hrange.1 hrange.2

def aBody : List AInstr := lift body

theorem aBody_defined (len k : Nat) (s : AState) :
    AllDefined len k s aBody := by
  rw [aBody, allDefined_lift]
  exact body_defined k s.regs

#print axioms body_defined
#print axioms body_outputs
#print axioms overflowBit_zero_range
#print axioms clean_output_sound
#print axioms aBody_defined

end LeanCompCert.Ports.Section413SignedAdd

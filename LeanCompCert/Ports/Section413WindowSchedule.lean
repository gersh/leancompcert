/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413SignedScale

/-!
# Constant-size runtime schedule for the Section 4.1.3 window scanner

The old certificate materialised every divisor event as generated Lean data.
The replacement rolled program has `99999 * 316` iterations and derives the
row `n` and trial divisor `s` from its compiled loop counter.  This module
proves the arithmetic scheduler once, symbolically; it never constructs the
production event list.
-/

namespace LeanCompCert.Ports.Section413WindowSchedule

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayScalarBlock

def slots : Nat := 316
def productionRows : Nat := 99999

def rN : Nat := 0
def rS : Nat := 1
def rQ : Nat := 2
def rRem : Nat := 3
def rSquare : Nat := 4
def rInRoot : Nat := 5
def rDivides : Nat := 6
def rActive : Nat := 7
def rPair : Nat := 8
def rEvenRem : Nat := 9
def rEven : Nat := 10
def rHalf : Nat := 11
def rHalfQ : Nat := 12
def rHalfRem : Nat := 13
def rHalfDivides : Nat := 14
def rHalfActive : Nat := 15
def rHalfPair : Nat := 16

def indexStage : List Instr :=
  [ .mov rN .idx
  , .binop rN .udiv (.reg rN) (.lit slots)
  , .binop rN .add (.reg rN) (.lit 1)
  , .mov rS .idx
  , .binop rS .urem (.reg rS) (.lit slots)
  , .binop rS .add (.reg rS) (.lit 1) ]

def divisorStage : List Instr :=
  [ .binop rQ .udiv (.reg rN) (.reg rS)
  , .binop rRem .urem (.reg rN) (.reg rS)
  , .binop rSquare .mul (.reg rS) (.reg rS)
  , .binop rInRoot .le (.reg rSquare) (.reg rN)
  , .binop rDivides .eq (.reg rRem) (.lit 0)
  , .binop rActive .mul (.reg rInRoot) (.reg rDivides)
  , .binop rPair .ne (.reg rQ) (.reg rS)
  , .binop rPair .mul (.reg rPair) (.reg rActive) ]

def halfStage : List Instr :=
  [ .binop rEvenRem .urem (.reg rN) (.lit 2)
  , .binop rEven .eq (.reg rEvenRem) (.lit 0)
  , .binop rHalf .udiv (.reg rN) (.lit 2)
  , .binop rHalfQ .udiv (.reg rHalf) (.reg rS)
  , .binop rHalfRem .urem (.reg rHalf) (.reg rS)
  , .binop rHalfDivides .eq (.reg rHalfRem) (.lit 0)
  , .binop rHalfActive .mul (.reg rEven) (.reg rInRoot)
  , .binop rHalfActive .mul (.reg rHalfActive) (.reg rHalfDivides)
  , .binop rHalfPair .ne (.reg rHalfQ) (.reg rS)
  , .binop rHalfPair .mul (.reg rHalfPair) (.reg rHalfActive) ]

def body : List AInstr := lift (indexStage ++ divisorStage ++ halfStage)

theorem indexStage_outputs (idx : Nat) (s : RegState)
    (hidx : idx < productionRows * slots) :
    let out := srun idx s indexStage
    out rN = idx / slots + 1 ∧ out rS = idx % slots + 1 := by
  dsimp only
  simp only [indexStage, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, Option.getD_some, rN, rS]
  simp only [slots] at hidx ⊢
  have hq : idx / 316 + 1 < M := by
    simp only [productionRows, M,
      LeanCompCert.Verified.MulWide.B64] at hidx ⊢
    omega
  have hr : idx % 316 + 1 < M := by
    have hm := Nat.mod_lt idx (by decide : 0 < 316)
    simp only [M, LeanCompCert.Verified.MulWide.B64]
    omega
  have hidxM : idx < M := by
    simp only [productionRows, M] at hidx ⊢
    omega
  simp [show 316 % M = 316 by decide,
    Nat.mod_eq_of_lt hidxM, Nat.mod_eq_of_lt hq,
    Nat.mod_eq_of_lt hr]

theorem divisorStage_outputs (idx : Nat) (s : RegState)
    (hn : 0 < s rN) (hnM : s rN < M)
    (hs : 0 < s rS) (hsM : s rS < M)
    (hsSq : s rS * s rS < M) :
    let out := srun idx s divisorStage
    out rQ = s rN / s rS ∧
      out rRem = s rN % s rS ∧
      out rActive = (if s rS * s rS ≤ s rN ∧ s rN % s rS = 0
        then 1 else 0) ∧
      out rPair = (if s rS * s rS ≤ s rN ∧ s rN % s rS = 0 ∧
        s rN / s rS ≠ s rS then 1 else 0) := by
  dsimp only
  simp only [rN, rS, rQ, rRem, rSquare, rInRoot, rDivides, rActive,
    rPair] at hn hnM hs hsM hsSq ⊢
  simp only [divisorStage, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rN, rS, rQ, rRem, rSquare, rInRoot, rDivides, rActive,
    rPair]
  simp only [Nat.reduceEqDiff, if_false, if_true]
  rw [if_neg (Nat.ne_of_gt hs), if_neg (Nat.ne_of_gt hs)]
  simp only [Option.getD_some]
  have hq : s 0 / s 1 < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnM
  have hr : s 0 % s 1 < M := Nat.lt_trans (Nat.mod_lt _ hs) hsM
  simp only [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hr,
    Nat.mod_eq_of_lt hsSq]
  by_cases hroot : s 1 * s 1 ≤ s 0 <;>
    by_cases hdiv : s 0 % s 1 = 0 <;>
    by_cases hpair : s 0 / s 1 ≠ s 1 <;>
    simp [hroot, hdiv, hpair, show 1 % M = 1 by decide]

theorem halfStage_outputs (idx : Nat) (s : RegState)
    (hnM : s rN < M) (hs : 0 < s rS) (hsM : s rS < M)
    (hinRoot : s rInRoot ≤ 1) :
    let out := srun idx s halfStage
    out rEven = (if s rN % 2 = 0 then 1 else 0) ∧
      out rHalf = s rN / 2 ∧
      out rHalfQ = (s rN / 2) / s rS ∧
      out rHalfActive =
        (if s rN % 2 = 0 ∧ s rInRoot = 1 ∧
          (s rN / 2) % s rS = 0 then 1 else 0) ∧
      out rHalfPair =
        (if s rN % 2 = 0 ∧ s rInRoot = 1 ∧
          (s rN / 2) % s rS = 0 ∧ (s rN / 2) / s rS ≠ s rS
        then 1 else 0) := by
  dsimp only
  simp only [rEvenRem, rEven, rHalf, rHalfQ, rHalfRem,
    rHalfDivides, rHalfActive, rHalfPair, rN, rS, rInRoot]
    at hnM hs hsM hinRoot ⊢
  simp only [halfStage, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rEvenRem, rEven, rHalf, rHalfQ, rHalfRem,
    rHalfDivides, rHalfActive, rHalfPair, rN, rS, rInRoot]
  simp only [Nat.reduceEqDiff, if_false, if_true]
  rw [if_neg (Nat.ne_of_gt hs), if_neg (Nat.ne_of_gt hs)]
  simp only [Option.getD_some]
  have hevenRem : s 0 % 2 < M := by
    exact Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  have hhalf : s 0 / 2 < M := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hnM
  have hq : s 0 / 2 / s 1 < M :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hhalf
  have hr : s 0 / 2 % s 1 < M := Nat.lt_trans (Nat.mod_lt _ hs) hsM
  simp only [show 2 % M = 2 by decide,
    Nat.mod_eq_of_lt hevenRem, Nat.mod_eq_of_lt hhalf,
    Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hr]
  rcases (by omega : s 5 = 0 ∨ s 5 = 1) with hroot | hroot <;>
    by_cases heven : s 0 % 2 = 0 <;>
    by_cases hdiv : s 0 / 2 % s 1 = 0 <;>
    by_cases hpair : s 0 / 2 / s 1 ≠ s 1 <;>
    simp [heven, hroot, hdiv, hpair, Nat.mod_eq_of_lt hq,
      Nat.mod_eq_of_lt hr, show 1 % M = 1 by decide]

def scheduleProgram (arrayLen rows : Nat) : AProgram :=
  { regCount := 328
    arrayLen := arrayLen
    loopCount := rows * slots
    init := []
    body := body
    epilogue := []
    output := rActive }

theorem scheduleProgram_wf (arrayLen rows : Nat) :
    (scheduleProgram arrayLen rows).WF := by
  refine ⟨by simp [scheduleProgram, rActive], by simp [scheduleProgram], ?_,
    by simp [scheduleProgram]⟩
  intro i hi
  exact (by decide : ∀ i ∈ body, i.WF 328) i hi

#print axioms indexStage_outputs
#print axioms divisorStage_outputs
#print axioms halfStage_outputs
#print axioms scheduleProgram_wf

end LeanCompCert.Ports.Section413WindowSchedule

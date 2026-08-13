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
open LeanCompCert.Verified.ArrayFoldBridge

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
def rHalfInRoot : Nat := 49

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
  , .binop rHalfInRoot .le (.reg rSquare) (.reg rHalf)
  , .binop rHalfQ .udiv (.reg rHalf) (.reg rS)
  , .binop rHalfRem .urem (.reg rHalf) (.reg rS)
  , .binop rHalfDivides .eq (.reg rHalfRem) (.lit 0)
  , .binop rHalfActive .mul (.reg rEven) (.reg rHalfInRoot)
  , .binop rHalfActive .mul (.reg rHalfActive) (.reg rHalfDivides)
  , .binop rHalfPair .ne (.reg rHalfQ) (.reg rS)
  , .binop rHalfPair .mul (.reg rHalfPair) (.reg rHalfActive) ]

def body : List AInstr := lift (indexStage ++ divisorStage ++ halfStage)

theorem indexStage_defined (idx : Nat) (s : RegState) :
    SAllDefined idx s indexStage := by
  simp [indexStage, SAllDefined, SDefined, denoteOperand, denoteOp, slots,
    RegState.set, sdest, sval, show 316 % M = 316 by decide]

theorem divisorStage_defined (idx : Nat) (s : RegState)
    (hs : 0 < s rS) : SAllDefined idx s divisorStage := by
  simp only [rS] at hs
  simp [divisorStage, SAllDefined, SDefined, denoteOperand, denoteOp,
    RegState.set, sdest, sval, rN, rS, rQ, rRem, rSquare, rInRoot,
    rDivides, rActive, rPair, Nat.ne_of_gt hs]

theorem halfStage_defined (idx : Nat) (s : RegState)
    (hs : 0 < s rS) : SAllDefined idx s halfStage := by
  simp only [rS] at hs
  simp [halfStage, SAllDefined, SDefined, denoteOperand, denoteOp,
    RegState.set, sdest, sval, rN, rS, rSquare, rEvenRem, rEven, rHalf,
    rHalfInRoot, rHalfQ, rHalfRem, rHalfDivides, rHalfActive, rHalfPair,
    Nat.ne_of_gt hs, show 2 % M = 2 by decide]

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

/-- The runtime scheduler is defined at every production iteration.  This is
symbolic in `idx`; it only proves that the literal and derived divisors are
nonzero. -/
theorem body_defined (len idx : Nat) (s : AState)
    (hidx : idx < productionRows * slots) :
    AllDefined len idx s body := by
  let a := srun idx s.regs indexStage
  have ha := indexStage_outputs idx s.regs hidx
  have haS : a rS = idx % slots + 1 := by
    simpa only [a] using ha.2
  have hframe : srun idx a divisorStage rS = a rS := by
    apply srun_untouched
    intro i hi
    simp only [divisorStage, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [sdest, rS, rQ, rRem, rSquare, rInRoot, rDivides, rActive, rPair]
  rw [body, lift_append, lift_append, AllDefined_append]
  refine ⟨?_, ?_⟩
  · rw [AllDefined_append]
    exact ⟨(allDefined_lift _ _ _ _).mpr (indexStage_defined idx s.regs),
      (allDefined_lift _ _ _ _).mpr
        (divisorStage_defined idx a (by rw [haS]; omega))⟩
  apply (allDefined_lift _ _ _ _).mpr
  apply halfStage_defined
  change 0 < srun idx a divisorStage rS
  rw [hframe, haS]
  omega

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
    (hsquare : s rSquare = s rS * s rS) :
    let out := srun idx s halfStage
    out rEven = (if s rN % 2 = 0 then 1 else 0) ∧
      out rHalf = s rN / 2 ∧
      out rHalfQ = (s rN / 2) / s rS ∧
      out rHalfActive =
        (if s rN % 2 = 0 ∧ s rS * s rS ≤ s rN / 2 ∧
          (s rN / 2) % s rS = 0 then 1 else 0) ∧
      out rHalfPair =
        (if s rN % 2 = 0 ∧ s rS * s rS ≤ s rN / 2 ∧
          (s rN / 2) % s rS = 0 ∧ (s rN / 2) / s rS ≠ s rS
        then 1 else 0) := by
  dsimp only
  simp only [rEvenRem, rEven, rHalf, rHalfQ, rHalfRem,
    rHalfDivides, rHalfActive, rHalfPair, rHalfInRoot, rN, rS,
    rSquare] at hnM hs hsM hsquare ⊢
  simp only [halfStage, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rEvenRem, rEven, rHalf, rHalfQ, rHalfRem,
    rHalfDivides, rHalfActive, rHalfPair, rHalfInRoot, rN, rS,
    rSquare]
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
  rw [hsquare]
  by_cases hroot : s 1 * s 1 ≤ s 0 / 2 <;>
    by_cases heven : s 0 % 2 = 0 <;>
    by_cases hdiv : s 0 / 2 % s 1 = 0 <;>
    by_cases hpair : s 0 / 2 / s 1 ≠ s 1 <;>
    simp [heven, hroot, hdiv, hpair, Nat.mod_eq_of_lt hq,
      Nat.mod_eq_of_lt hr, show 1 % M = 1 by decide]

/-- Mathematical schedule decoded from one flat loop index. -/
structure Slot where
  n : Nat
  s : Nat
  q : Nat
  active : Nat
  pair : Nat
  halfQ : Nat
  halfActive : Nat
  halfPair : Nat
  deriving DecidableEq, Repr

def slotAt (idx : Nat) : Slot :=
  let n := idx / slots + 1
  let s := idx % slots + 1
  { n := n
    s := s
    q := n / s
    active := if s * s ≤ n ∧ n % s = 0 then 1 else 0
    pair := if s * s ≤ n ∧ n % s = 0 ∧ n / s ≠ s then 1 else 0
    halfQ := (n / 2) / s
    halfActive := if n % 2 = 0 ∧ s * s ≤ n / 2 ∧ (n / 2) % s = 0
      then 1 else 0
    halfPair := if n % 2 = 0 ∧ s * s ≤ n / 2 ∧
        (n / 2) % s = 0 ∧ (n / 2) / s ≠ s then 1 else 0 }

private theorem srun_stage_frame (idx : Nat) (st : RegState)
    (stage : List Instr) (r : Nat)
    (h : ∀ i ∈ stage, sdest i ≠ r) :
    srun idx st stage r = st r := by
  apply srun_untouched
  intro i hi
  exact h i hi

/-- The fixed compiled scheduling block produces `slotAt idx`.  This theorem
is symbolic in `idx`; it does not enumerate any production row. -/
theorem body_outputs (idx : Nat) (st : AState)
    (hidx : idx < productionRows * slots) :
    let out := arun idx st body
    out.regs rN = (slotAt idx).n ∧
      out.regs rS = (slotAt idx).s ∧
      out.regs rQ = (slotAt idx).q ∧
      out.regs rActive = (slotAt idx).active ∧
      out.regs rPair = (slotAt idx).pair ∧
      out.regs rHalfQ = (slotAt idx).halfQ ∧
      out.regs rHalfActive = (slotAt idx).halfActive ∧
      out.regs rHalfPair = (slotAt idx).halfPair := by
  dsimp only
  let a := srun idx st.regs indexStage
  let b := srun idx a divisorStage
  have ha := indexStage_outputs idx st.regs hidx
  have han : a rN = idx / slots + 1 := by simpa [a] using ha.1
  have has : a rS = idx % slots + 1 := by simpa [a] using ha.2
  have hnPos : 0 < a rN := by rw [han]; exact Nat.succ_pos _
  have hnM : a rN < M := by
    rw [han]
    have hrow : idx / slots < productionRows := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < slots)).2
      simpa [Nat.mul_comm] using hidx
    simp only [productionRows, M] at hrow ⊢
    omega
  have hsPos : 0 < a rS := by rw [has]; exact Nat.succ_pos _
  have hsM : a rS < M := by
    rw [has]
    have hle : idx % slots + 1 ≤ 316 := by
      have hm := Nat.mod_lt idx (by decide : 0 < slots)
      simpa only [slots] using Nat.succ_le_of_lt hm
    exact Nat.lt_of_le_of_lt hle (by decide)
  have hsSqM : a rS * a rS < M := by
    rw [has]
    have hle : idx % slots + 1 ≤ 316 := by
      have hm := Nat.mod_lt idx (by decide : 0 < slots)
      simpa only [slots] using Nat.succ_le_of_lt hm
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hle hle) (by decide)
  have hb := divisorStage_outputs idx a hnPos hnM hsPos hsM hsSqM
  have hbn : b rN = a rN := by
    apply srun_stage_frame
    intro i hi
    simp only [divisorStage, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sdest, rN] <;> decide
  have hbs : b rS = a rS := by
    apply srun_stage_frame
    intro i hi
    simp only [divisorStage, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sdest, rS] <;> decide
  have hbSquare : b rSquare = a rS * a rS := by
    simp only [b, divisorStage, srun, sdest, sval, denoteOperand, denoteOp,
      Option.getD_some, RegState.set, rN, rS, rQ, rRem, rSquare, rInRoot,
      rDivides, rActive, rPair, Nat.reduceEqDiff, if_false, if_true]
    exact Nat.mod_eq_of_lt hsSqM
  have hc := halfStage_outputs idx b (by simpa [hbn] using hnM)
    (by simpa [hbs] using hsPos) (by simpa [hbs] using hsM)
    (by simpa [hbs] using hbSquare)
  have hbq : b rQ = (idx / slots + 1) / (idx % slots + 1) := by
    simpa [b, han, has] using hb.1
  have hbactive : b rActive =
      (if (idx % slots + 1) * (idx % slots + 1) ≤ idx / slots + 1 ∧
        (idx / slots + 1) % (idx % slots + 1) = 0 then 1 else 0) := by
    simpa [b, han, has] using hb.2.2.1
  have hbpair : b rPair =
      (if (idx % slots + 1) * (idx % slots + 1) ≤ idx / slots + 1 ∧
        (idx / slots + 1) % (idx % slots + 1) = 0 ∧
        (idx / slots + 1) / (idx % slots + 1) ≠ idx % slots + 1
      then 1 else 0) := by
    simpa [b, han, has] using hb.2.2.2
  have hcq : srun idx b halfStage rHalfQ =
      (idx / slots + 1) / 2 / (idx % slots + 1) := by
    simpa [hbn, hbs, han, has] using hc.2.2.1
  have hcactive : srun idx b halfStage rHalfActive =
      (if (idx / slots + 1) % 2 = 0 ∧
        (idx % slots + 1) * (idx % slots + 1) ≤ (idx / slots + 1) / 2 ∧
        (idx / slots + 1) / 2 % (idx % slots + 1) = 0
      then 1 else 0) := by
    simpa [hbn, hbs, han, has] using hc.2.2.2.1
  have hcpair : srun idx b halfStage rHalfPair =
      (if (idx / slots + 1) % 2 = 0 ∧
        (idx % slots + 1) * (idx % slots + 1) ≤ (idx / slots + 1) / 2 ∧
        (idx / slots + 1) / 2 % (idx % slots + 1) = 0 ∧
        (idx / slots + 1) / 2 / (idx % slots + 1) ≠ idx % slots + 1
      then 1 else 0) := by
    simpa [hbn, hbs, han, has] using hc.2.2.2.2
  have frameHalf (r : Nat)
      (hr0 : r ≠ rEvenRem) (hr1 : r ≠ rEven) (hr2 : r ≠ rHalf)
      (hr3 : r ≠ rHalfQ) (hr4 : r ≠ rHalfRem)
      (hr5 : r ≠ rHalfDivides) (hr6 : r ≠ rHalfActive)
      (hr7 : r ≠ rHalfPair) (hr8 : r ≠ rHalfInRoot) :
      srun idx b halfStage r = b r := by
    apply srun_stage_frame
    intro i hi
    simp only [halfStage, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sdest] <;> omega
  rw [body, arun_lift]
  simp only [srun_append]
  change (srun idx b halfStage rN = _ ∧
    srun idx b halfStage rS = _ ∧
    srun idx b halfStage rQ = _ ∧
    srun idx b halfStage rActive = _ ∧
    srun idx b halfStage rPair = _ ∧
    srun idx b halfStage rHalfQ = _ ∧
    srun idx b halfStage rHalfActive = _ ∧
    srun idx b halfStage rHalfPair = _)
  simp only [slotAt]
  rw [frameHalf rN (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    frameHalf rS (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    frameHalf rQ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    frameHalf rActive (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    frameHalf rPair (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    hbn, hbs, han, has, hbq, hbactive, hbpair, hcq, hcactive, hcpair]
  simp

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
#print axioms body_defined
#print axioms divisorStage_outputs
#print axioms halfStage_outputs
#print axioms body_outputs
#print axioms scheduleProgram_wf

end LeanCompCert.Ports.Section413WindowSchedule

/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowTableRead
import LeanCompCert.Verified.ArrayRegFrame

/-!
# Compiled outward division of a signed interval cell

This adapter runs the verified signed divider twice.  `negate = false`
computes outward division of `[lo,hi]`; `negate = true` swaps and negates the
endpoints first, as required by the K1 first-divisor term.  The final gate is
a compiled zero/one event gate, so inactive speculative work contributes the
zero cell without branching.
-/

namespace LeanCompCert.Ports.Section413WindowCellDiv

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.Section413Cells

def rInLo : Nat := 32
def rInHi : Nat := 33
def rDen : Nat := 34
def rGate : Nat := 35
def rOutLo : Nat := 36
def rOutHi : Nat := 37

def loadWord (src : Nat) (negate : Bool) : List Instr :=
  [ .mov LeanCompCert.Ports.Section413SignedDiv.rDiv (.reg rDen)
  , if negate then .binop LeanCompCert.Ports.Section413SignedDiv.rWord
      .sub (.lit 0) (.reg src)
    else .mov LeanCompCert.Ports.Section413SignedDiv.rWord (.reg src) ]

def lowerStage (negate : Bool) : List AInstr :=
  lift (loadWord (if negate then rInHi else rInLo) negate) ++
    LeanCompCert.Ports.Section413SignedDiv.aBody ++
      lift [.mov rOutLo (.reg LeanCompCert.Ports.Section413SignedDiv.rFloor)]

def upperStage (negate : Bool) : List AInstr :=
  lift (loadWord (if negate then rInLo else rInHi) negate) ++
    LeanCompCert.Ports.Section413SignedDiv.aBody ++
      lift [.mov rOutHi (.reg LeanCompCert.Ports.Section413SignedDiv.rCeil)]

def gateStage : List Instr :=
  [ .binop rOutLo .mul (.reg rOutLo) (.reg rGate)
  , .binop rOutHi .mul (.reg rOutHi) (.reg rGate) ]

def body (negate : Bool) : List AInstr :=
  lowerStage negate ++ upperStage negate ++ lift gateStage

theorem loadWord_outputs (k : Nat) (s : RegState) (src : Nat)
    (negate : Bool) (hsrcNe : src ≠
      LeanCompCert.Ports.Section413SignedDiv.rDiv) :
    let out := srun k s (loadWord src negate)
    out LeanCompCert.Ports.Section413SignedDiv.rDiv = s rDen ∧
      out LeanCompCert.Ports.Section413SignedDiv.rWord = if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0 (s src) else s src := by
  dsimp only
  simp only [LeanCompCert.Ports.Section413SignedDiv.rDiv] at hsrcNe
  cases negate <;>
    simp [loadWord, srun, sdest, sval, denoteOperand, denoteOp,
      RegState.set, LeanCompCert.Ports.Section413SignedDiv.rDiv,
      LeanCompCert.Ports.Section413SignedDiv.rWord, rDen,
      LeanCompCert.Ports.Section413G1Program.tsub, hsrcNe]

theorem lowerStage_defined (len k : Nat) (s : AState) (negate : Bool)
    (hden : 0 < s.regs rDen) :
    AllDefined len k s (lowerStage negate) := by
  let p := arun k s (lift (loadWord
    (if negate then rInHi else rInLo) negate))
  have hload := loadWord_outputs k s.regs
    (if negate then rInHi else rInLo) negate
    (by cases negate <;> decide)
  have hpDen : p.regs LeanCompCert.Ports.Section413SignedDiv.rDiv =
      s.regs rDen := by
    simpa [p, arun_lift] using hload.1
  rw [lowerStage, AllDefined_append]
  refine ⟨?_, allDefined_lift_of_noDiv len k _ _ (by decide)⟩
  rw [AllDefined_append]
  exact ⟨allDefined_lift_of_noDiv len k _ s
      (by cases negate <;> decide),
    LeanCompCert.Ports.Section413SignedDiv.aBody_defined len k p
      (by simpa [hpDen] using hden)⟩

theorem upperStage_defined (len k : Nat) (s : AState) (negate : Bool)
    (hden : 0 < s.regs rDen) :
    AllDefined len k s (upperStage negate) := by
  let p := arun k s (lift (loadWord
    (if negate then rInLo else rInHi) negate))
  have hload := loadWord_outputs k s.regs
    (if negate then rInLo else rInHi) negate
    (by cases negate <;> decide)
  have hpDen : p.regs LeanCompCert.Ports.Section413SignedDiv.rDiv =
      s.regs rDen := by
    simpa [p, arun_lift] using hload.1
  rw [upperStage, AllDefined_append]
  refine ⟨?_, allDefined_lift_of_noDiv len k _ _ (by decide)⟩
  rw [AllDefined_append]
  exact ⟨allDefined_lift_of_noDiv len k _ s
      (by cases negate <;> decide),
    LeanCompCert.Ports.Section413SignedDiv.aBody_defined len k p
      (by simpa [hpDen] using hden)⟩

theorem body_defined (len k : Nat) (s : AState) (negate : Bool)
    (hden : 0 < s.regs rDen) : AllDefined len k s (body negate) := by
  let p := arun k s (lowerStage negate)
  have hpDen : p.regs rDen = s.regs rDen := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rDen (lowerStage negate) (by cases negate <;> decide) s
  rw [body, AllDefined_append]
  refine ⟨?_, allDefined_lift_of_noDiv len k _ _ (by decide)⟩
  rw [AllDefined_append]
  exact ⟨lowerStage_defined len k s negate hden,
    upperStage_defined len k p negate (by simpa [hpDen] using hden)⟩

theorem one_lower_outputs (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hden : 0 < s.regs rDen) :
    let out := arun k s (lowerStage negate)
    out.regs rOutLo =
      LeanCompCert.Ports.Section413SignedDiv.floorMag
        (if negate then LeanCompCert.Ports.Section413G1Program.tsub 0
          (s.regs rInHi) else s.regs rInLo)
        (s.regs rDen) ∧ out.arr = s.arr := by
  dsimp only
  let p := arun k s (lift (loadWord (if negate then rInHi else rInLo) negate))
  let q := arun k p LeanCompCert.Ports.Section413SignedDiv.aBody
  have hsrcM : s.regs (if negate then rInHi else rInLo) < M := by
    cases negate with
    | false => exact hword rInLo
    | true => exact hword rInHi
  have hload := loadWord_outputs k s.regs
    (if negate then rInHi else rInLo) negate
    (by cases negate <;> decide)
  have hpWord : p.regs LeanCompCert.Ports.Section413SignedDiv.rWord =
      if negate then LeanCompCert.Ports.Section413G1Program.tsub 0
        (s.regs rInHi) else s.regs rInLo := by
    by_cases hneg : negate = true <;>
      simp [hneg, p, arun_lift] at hload ⊢
    · exact hload.2
    · exact hload.2
  have hpDen : p.regs LeanCompCert.Ports.Section413SignedDiv.rDiv =
      s.regs rDen := by
    simpa [p, arun_lift] using hload.1
  have hpWordM : p.regs LeanCompCert.Ports.Section413SignedDiv.rWord < M := by
    rw [hpWord]
    cases negate
    · exact hword rInLo
    · exact LeanCompCert.Ports.Section413G1Sound.tsub_lt _ _
  have hpDenPos : 0 < p.regs LeanCompCert.Ports.Section413SignedDiv.rDiv := by
    simpa [hpDen] using hden
  have hpDenM : p.regs LeanCompCert.Ports.Section413SignedDiv.rDiv < M := by
    rw [hpDen]; exact hword rDen
  have hdiv := LeanCompCert.Ports.Section413SignedDiv.aBody_outputs
    k p hpWordM hpDenPos hpDenM
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hqword : ∀ j, q.regs j < M := arun_regs_word k _ _ hpword hparray
  rw [lowerStage, arun_append, arun_append, arun_lift]
  change srun k q.regs
    [.mov rOutLo (.reg LeanCompCert.Ports.Section413SignedDiv.rFloor)]
      rOutLo = _ ∧ _
  simp only [srun, sdest, sval, denoteOperand, RegState.set, rOutLo,
    if_pos]
  refine ⟨?_, ?_⟩
  · simpa [q, hpWord, hpDen] using hdiv.1
  · simpa [q, p, arun_lift] using hdiv.2.2

theorem one_upper_outputs (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hden : 0 < s.regs rDen) :
    let out := arun k s (upperStage negate)
    out.regs rOutHi =
      LeanCompCert.Ports.Section413SignedDiv.ceilMag
        (if negate then LeanCompCert.Ports.Section413G1Program.tsub 0
          (s.regs rInLo) else s.regs rInHi)
        (s.regs rDen) ∧ out.arr = s.arr := by
  dsimp only
  let p := arun k s (lift (loadWord (if negate then rInLo else rInHi) negate))
  let q := arun k p LeanCompCert.Ports.Section413SignedDiv.aBody
  have hsrcM : s.regs (if negate then rInLo else rInHi) < M := by
    cases negate with
    | false => exact hword rInHi
    | true => exact hword rInLo
  have hload := loadWord_outputs k s.regs
    (if negate then rInLo else rInHi) negate
    (by cases negate <;> decide)
  have hpWord : p.regs LeanCompCert.Ports.Section413SignedDiv.rWord =
      if negate then LeanCompCert.Ports.Section413G1Program.tsub 0
        (s.regs rInLo) else s.regs rInHi := by
    by_cases hneg : negate = true <;>
      simp [hneg, p, arun_lift] at hload ⊢
    · exact hload.2
    · exact hload.2
  have hpDen : p.regs LeanCompCert.Ports.Section413SignedDiv.rDiv =
      s.regs rDen := by
    simpa [p, arun_lift] using hload.1
  have hpWordM : p.regs LeanCompCert.Ports.Section413SignedDiv.rWord < M := by
    rw [hpWord]
    cases negate
    · exact hword rInHi
    · exact LeanCompCert.Ports.Section413G1Sound.tsub_lt _ _
  have hpDenPos : 0 < p.regs LeanCompCert.Ports.Section413SignedDiv.rDiv := by
    simpa [hpDen] using hden
  have hpDenM : p.regs LeanCompCert.Ports.Section413SignedDiv.rDiv < M := by
    rw [hpDen]; exact hword rDen
  have hdiv := LeanCompCert.Ports.Section413SignedDiv.aBody_outputs
    k p hpWordM hpDenPos hpDenM
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hqword : ∀ j, q.regs j < M := arun_regs_word k _ _ hpword hparray
  rw [upperStage, arun_append, arun_append, arun_lift]
  change srun k q.regs
    [.mov rOutHi (.reg LeanCompCert.Ports.Section413SignedDiv.rCeil)]
      rOutHi = _ ∧ _
  simp only [srun, sdest, sval, denoteOperand, RegState.set, rOutHi,
    if_pos]
  refine ⟨?_, ?_⟩
  · simpa [q, hpWord, hpDen] using hdiv.2.1
  · simpa [q, p, arun_lift] using hdiv.2.2

/-- The constant-size compiled adapter computes both outward endpoints and
then applies the runtime event gate.  This theorem is symbolic in the cell,
divisor, and gate; it performs no production-range evaluation in Lean. -/
theorem body_outputs (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hden : 0 < s.regs rDen) :
    let out := arun k s (body negate)
    out.regs rOutLo =
        (LeanCompCert.Ports.Section413SignedDiv.floorMag
          (if negate then LeanCompCert.Ports.Section413G1Program.tsub 0
            (s.regs rInHi) else s.regs rInLo)
          (s.regs rDen) * s.regs rGate) % M ∧
      out.regs rOutHi =
        (LeanCompCert.Ports.Section413SignedDiv.ceilMag
          (if negate then LeanCompCert.Ports.Section413G1Program.tsub 0
            (s.regs rInLo) else s.regs rInHi)
          (s.regs rDen) * s.regs rGate) % M ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s (lowerStage negate)
  let q := arun k p (upperStage negate)
  have hlow := one_lower_outputs k s negate hword harray hden
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpDen : p.regs rDen = s.regs rDen := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rDen (lowerStage negate) (by cases negate <;> decide) s
  have hpInLo : p.regs rInLo = s.regs rInLo := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rInLo (lowerStage negate) (by cases negate <;> decide) s
  have hpInHi : p.regs rInHi = s.regs rInHi := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rInHi (lowerStage negate) (by cases negate <;> decide) s
  have hpGate : p.regs rGate = s.regs rGate := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rGate (lowerStage negate) (by cases negate <;> decide) s
  have hupper := one_upper_outputs k p negate hpword hparray (by
    simpa [hpDen] using hden)
  have hqOutLo : q.regs rOutLo = p.regs rOutLo := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rOutLo (upperStage negate) (by cases negate <;> decide) p
  have hqGate : q.regs rGate = s.regs rGate := by
    rw [LeanCompCert.Verified.ArrayRegFrame.arun_frame
      k rGate (upperStage negate) (by cases negate <;> decide) p, hpGate]
  have hqLo : q.regs rOutLo =
      LeanCompCert.Ports.Section413SignedDiv.floorMag
        (if negate then LeanCompCert.Ports.Section413G1Program.tsub 0
          (s.regs rInHi) else s.regs rInLo) (s.regs rDen) :=
    hqOutLo.trans hlow.1
  have hqHi : q.regs rOutHi =
      LeanCompCert.Ports.Section413SignedDiv.ceilMag
        (if negate then LeanCompCert.Ports.Section413G1Program.tsub 0
          (s.regs rInLo) else s.regs rInHi) (s.regs rDen) := by
    simpa [q, hpInLo, hpInHi, hpDen] using hupper.1
  have hqword : ∀ j, q.regs j < M := arun_regs_word k _ _ hpword hparray
  rw [body, arun_append, arun_append, arun_lift]
  change srun k q.regs gateStage rOutLo = _ ∧
    srun k q.regs gateStage rOutHi = _ ∧ _
  simp only [gateStage, srun, sdest, sval, denoteOperand, denoteOp,
    Option.getD_some, RegState.set, rOutLo, rOutHi,
    rGate, Nat.reduceEqDiff, if_false, if_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [show q.regs 36 = q.regs rOutLo by rfl, hqLo,
      show q.regs 35 = q.regs rGate by rfl, hqGate]
    rfl
  · rw [show q.regs 37 = q.regs rOutHi by rfl, hqHi,
      show q.regs 35 = q.regs rGate by rfl, hqGate]
    rfl
  · simpa [q, p] using hupper.2.trans hlow.2

theorem body_outputs_gate_one (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hden : 0 < s.regs rDen) (hgate : s.regs rGate = 1) :
    let out := arun k s (body negate)
    out.regs rOutLo = encodeZ
        (decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInHi)
        else s.regs rInLo) / (s.regs rDen : Int)) ∧
      out.regs rOutHi = encodeZ
        (-((-decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInLo)
        else s.regs rInHi)) / (s.regs rDen : Int))) ∧
      out.arr = s.arr := by
  dsimp only
  have h := body_outputs k s negate hword harray hden
  have hloWord : (if negate then
      LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInHi)
      else s.regs rInLo) < M := by
    cases negate
    · exact hword rInLo
    · exact LeanCompCert.Ports.Section413G1Sound.tsub_lt _ _
  have hhiWord : (if negate then
      LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInLo)
      else s.regs rInHi) < M := by
    cases negate
    · exact hword rInHi
    · exact LeanCompCert.Ports.Section413G1Sound.tsub_lt _ _
  refine ⟨?_, ?_, h.2.2⟩
  · rw [h.1,
      LeanCompCert.Ports.Section413SignedDiv.floorMag_eq_source _ _
        hloWord hden,
      hgate, Nat.mul_one,
      Nat.mod_eq_of_lt
        (LeanCompCert.Ports.Section413G1Sound.encodeZ_lt_M _)]
  · rw [h.2.1,
      LeanCompCert.Ports.Section413SignedDiv.ceilMag_eq_source _ _
        hhiWord hden,
      hgate, Nat.mul_one,
      Nat.mod_eq_of_lt
        (LeanCompCert.Ports.Section413G1Sound.encodeZ_lt_M _)]

theorem body_outputs_gate_zero (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hden : 0 < s.regs rDen) (hgate : s.regs rGate = 0) :
    let out := arun k s (body negate)
    out.regs rOutLo = 0 ∧ out.regs rOutHi = 0 ∧ out.arr = s.arr := by
  dsimp only
  have h := body_outputs k s negate hword harray hden
  rw [h.1, h.2.1, hgate, Nat.mul_zero, Nat.zero_mod]
  exact ⟨rfl, rfl, h.2.2⟩

theorem body_outputs_gate_one_decoded (k : Nat) (s : AState)
    (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hden : 0 < s.regs rDen) (hgate : s.regs rGate = 1) :
    let out := arun k s (body negate)
    decodeZ (out.regs rOutLo) =
        decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInHi)
        else s.regs rInLo) / (s.regs rDen : Int) ∧
      decodeZ (out.regs rOutHi) =
        -((-decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInLo)
        else s.regs rInHi)) / (s.regs rDen : Int)) ∧
      out.arr = s.arr := by
  dsimp only
  have h := body_outputs_gate_one k s negate hword harray hden hgate
  have hloWord : (if negate then
      LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInHi)
      else s.regs rInLo) < M := by
    cases negate
    · exact hword rInLo
    · exact LeanCompCert.Ports.Section413G1Sound.tsub_lt _ _
  have hhiWord : (if negate then
      LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInLo)
      else s.regs rInHi) < M := by
    cases negate
    · exact hword rInHi
    · exact LeanCompCert.Ports.Section413G1Sound.tsub_lt _ _
  rw [h.1, h.2.1,
    decodeZ_encodeZ _
      (LeanCompCert.Ports.Section413SignedDiv.floorSource_range _ _
        hloWord hden).1
      (LeanCompCert.Ports.Section413SignedDiv.floorSource_range _ _
        hloWord hden).2,
    decodeZ_encodeZ _
      (LeanCompCert.Ports.Section413SignedDiv.ceilSource_range _ _
        hhiWord hden).1
      (LeanCompCert.Ports.Section413SignedDiv.ceilSource_range _ _
        hhiWord hden).2]
  exact ⟨rfl, rfl, h.2.2⟩

def program (arrayLen loopCount : Nat) (negate : Bool) : AProgram :=
  { regCount := 328
    arrayLen := arrayLen
    loopCount := loopCount
    init := []
    body := body negate
    epilogue := []
    output := rOutHi }

theorem program_wf (arrayLen loopCount : Nat) (negate : Bool) :
    (program arrayLen loopCount negate).WF := by
  refine ⟨by simp [program, rOutHi], by simp [program], ?_, by simp [program]⟩
  intro i hi
  cases negate with
  | false => exact (by decide : ∀ i ∈ body false, i.WF 328) i hi
  | true => exact (by decide : ∀ i ∈ body true, i.WF 328) i hi

#print axioms loadWord_outputs
#print axioms body_defined
#print axioms one_lower_outputs
#print axioms one_upper_outputs
#print axioms body_outputs
#print axioms body_outputs_gate_one
#print axioms body_outputs_gate_zero
#print axioms body_outputs_gate_one_decoded
#print axioms program_wf

end LeanCompCert.Ports.Section413WindowCellDiv

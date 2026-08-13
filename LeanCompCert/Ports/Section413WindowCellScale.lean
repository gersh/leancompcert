/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import LeanCompCert.Ports.Section413WindowCellDiv
import LeanCompCert.Ports.Section413SignedScale

/-!
# Compiled checked scaling of a signed interval cell

The Section 4.1.3 K2 terms scale table differences by a runtime natural
factor.  This adapter invokes the checked signed multiplier for one endpoint
and saves its result for the scanner.  Its correctness theorem is symbolic:
when the compiled sticky overflow flag remains clear, the saved word encodes
the exact mathematical product.  No production table or scan is evaluated
by Lean.
-/

namespace LeanCompCert.Ports.Section413WindowCellScale

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Ports.Section413Cells

def rInLo : Nat := LeanCompCert.Ports.Section413WindowCellDiv.rInLo
def rInHi : Nat := LeanCompCert.Ports.Section413WindowCellDiv.rInHi
def rFactor : Nat := LeanCompCert.Ports.Section413WindowCellDiv.rDen
def rGate : Nat := LeanCompCert.Ports.Section413WindowCellDiv.rGate
def rOutLo : Nat := LeanCompCert.Ports.Section413WindowCellDiv.rOutLo
def rOutHi : Nat := LeanCompCert.Ports.Section413WindowCellDiv.rOutHi

def loadWord (src : Nat) (negate : Bool) : List Instr :=
  LeanCompCert.Ports.Section413WindowCellDiv.loadWord src negate

def oneStage (src dest : Nat) (negate : Bool) : List AInstr :=
  lift (loadWord src negate) ++
    LeanCompCert.Ports.Section413SignedScale.body ++
      lift [.mov dest (.reg LeanCompCert.Ports.Section413SignedScale.rOut)]

def gateStage : List Instr :=
  [ .binop rOutLo .mul (.reg rOutLo) (.reg rGate)
  , .binop rOutHi .mul (.reg rOutHi) (.reg rGate) ]

def body (negate : Bool) : List AInstr :=
  oneStage (if negate then rInHi else rInLo) rOutLo negate ++
    oneStage (if negate then rInLo else rInHi) rOutHi negate ++
      lift gateStage

/-- One literal checked multiplier invocation saves the exact encoded signed
product when its own compiled sticky flag is clear. -/
theorem oneStage_clean_output (k : Nat) (s : AState) (src dest : Nat)
    (negate : Bool)
    (hsrcNe : src ≠ LeanCompCert.Ports.Section413SignedDiv.rDiv)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hclean :
      (arun k
        (arun k s (lift (loadWord src negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0) :
    let out := arun k s (oneStage src dest negate)
    out.regs dest = encodeZ
        ((s.regs rFactor : Int) *
          decodeZ (if negate then
            LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs src)
          else s.regs src)) ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s (lift (loadWord src negate))
  let q := arun k p LeanCompCert.Ports.Section413SignedScale.body
  have hload := LeanCompCert.Ports.Section413WindowCellDiv.loadWord_outputs
    k s.regs src negate hsrcNe
  have hpWord : p.regs LeanCompCert.Ports.Section413SignedScale.rWord =
      if negate then LeanCompCert.Ports.Section413G1Program.tsub 0
        (s.regs src) else s.regs src := by
    by_cases hneg : negate = true <;>
      simp [hneg, p, arun_lift, loadWord] at hload ⊢
    · exact hload.2
    · exact hload.2
  have hpFactor : p.regs LeanCompCert.Ports.Section413SignedScale.rFactor =
      s.regs rFactor := by
    simpa [p, arun_lift, loadWord, rFactor,
      LeanCompCert.Ports.Section413SignedScale.rFactor] using hload.1
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hscale :=
    LeanCompCert.Ports.Section413SignedScale.body_clean_output_encoded
      k p hpword hparray (by simpa [q, p] using hclean)
  have hqword : ∀ j, q.regs j < M := arun_regs_word k _ _ hpword hparray
  rw [oneStage, arun_append, arun_append, arun_lift]
  change srun k q.regs
    [.mov dest (.reg LeanCompCert.Ports.Section413SignedScale.rOut)] dest = _ ∧ _
  simp only [srun, sdest, sval, denoteOperand, RegState.set, if_pos]
  refine ⟨?_, ?_⟩
  · simpa [q, hpWord, hpFactor] using hscale
  · simpa [q, p, arun_lift] using
      (show q.arr = s.arr from rfl)

/-- The same one-stage adapter exposes the signed-range certificate supplied
by the checked multiplier. -/
theorem oneStage_clean_output_range (k : Nat) (s : AState) (src dest : Nat)
    (negate : Bool)
    (hsrcNe : src ≠ LeanCompCert.Ports.Section413SignedDiv.rDiv)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hclean :
      (arun k
        (arun k s (lift (loadWord src negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0) :
    let z := (s.regs rFactor : Int) *
      decodeZ (if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs src)
      else s.regs src)
    let out := arun k s (oneStage src dest negate)
    out.regs dest = encodeZ z ∧
      (- (H63 : Int)) ≤ z ∧ z < (H63 : Int) ∧ out.arr = s.arr := by
  dsimp only
  let p := arun k s (lift (loadWord src negate))
  have hload := LeanCompCert.Ports.Section413WindowCellDiv.loadWord_outputs
    k s.regs src negate hsrcNe
  have hpWord : p.regs LeanCompCert.Ports.Section413SignedScale.rWord =
      if negate then LeanCompCert.Ports.Section413G1Program.tsub 0
        (s.regs src) else s.regs src := by
    by_cases hneg : negate = true <;>
      simp [hneg, p, arun_lift, loadWord] at hload ⊢
    · exact hload.2
    · exact hload.2
  have hpFactor : p.regs LeanCompCert.Ports.Section413SignedScale.rFactor =
      s.regs rFactor := by
    simpa [p, arun_lift, loadWord, rFactor,
      LeanCompCert.Ports.Section413SignedScale.rFactor] using hload.1
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hout := oneStage_clean_output k s src dest negate hsrcNe hword harray
    hclean
  have hrange := LeanCompCert.Ports.Section413SignedScale.body_clean_product_range
    k p hpword hparray (by simpa [p] using hclean)
  refine ⟨hout.1, ?_, ?_, hout.2⟩
  · simpa [hpFactor, hpWord] using hrange.1
  · simpa [hpFactor, hpWord] using hrange.2

def program (arrayLen loopCount : Nat) (negate : Bool) : AProgram :=
  { regCount := 328
    arrayLen := arrayLen
    loopCount := loopCount
    init := []
    body := body negate
    epilogue := []
    output := LeanCompCert.Ports.Section413SignedScale.rViol }

theorem program_wf (arrayLen loopCount : Nat) (negate : Bool) :
    (program arrayLen loopCount negate).WF := by
  refine ⟨by simp [program, LeanCompCert.Ports.Section413SignedScale.rViol],
    by simp [program], ?_, by simp [program]⟩
  intro i hi
  cases negate with
  | false => exact (by decide : ∀ i ∈ body false, i.WF 328) i hi
  | true => exact (by decide : ∀ i ∈ body true, i.WF 328) i hi

#print axioms oneStage_clean_output
#print axioms oneStage_clean_output_range
#print axioms program_wf

end LeanCompCert.Ports.Section413WindowCellScale

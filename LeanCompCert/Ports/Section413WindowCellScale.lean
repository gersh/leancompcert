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
      LeanCompCert.Ports.Section413SignedScale.rFactor,
      LeanCompCert.Ports.Section413WindowCellDiv.rDen,
      LeanCompCert.Ports.Section413SignedDiv.rDiv] using hload.1
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

theorem oneStage_factor_frame (k : Nat) (s : AState) (src dest : Nat)
    (negate : Bool) (hdest : dest ≠ rFactor) :
    (arun k s (oneStage src dest negate)).regs rFactor = s.regs rFactor := by
  let p := arun k s (lift (loadWord src negate))
  let q := arun k p LeanCompCert.Ports.Section413SignedScale.body
  have hpFactor : p.regs rFactor = s.regs rFactor := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rFactor
      (lift (loadWord src negate)) (by
        cases negate <;>
          simp [lift, loadWord,
            LeanCompCert.Ports.Section413WindowCellDiv.loadWord,
            LeanCompCert.Verified.ArrayRegFrame.writes,
            LeanCompCert.Verified.ArrayRegFrame.instrWrites, rFactor,
            LeanCompCert.Ports.Section413WindowCellDiv.rDen,
            LeanCompCert.Ports.Section413SignedDiv.rDiv,
            LeanCompCert.Ports.Section413SignedDiv.rWord]) s
  have hqFactor : q.regs rFactor = p.regs rFactor := by
    exact LeanCompCert.Verified.ArrayRegFrame.arun_frame k rFactor
      LeanCompCert.Ports.Section413SignedScale.body (by decide) p
  rw [oneStage, arun_append, arun_append, arun_lift]
  change srun k q.regs
    [.mov dest (.reg LeanCompCert.Ports.Section413SignedScale.rOut)]
      rFactor = _
  rw [srun_untouched]
  · exact hqFactor.trans hpFactor
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    simpa only [sdest] using hdest

private theorem oneStage_frame_of (k r : Nat) (s : AState)
    (src dest : Nat) (negate : Bool)
    (hload : LeanCompCert.Verified.ArrayRegFrame.writes r
      (lift (loadWord src negate)) = false)
    (hscale : LeanCompCert.Verified.ArrayRegFrame.writes r
      LeanCompCert.Ports.Section413SignedScale.body = false)
    (hdest : dest ≠ r) :
    (arun k s (oneStage src dest negate)).regs r = s.regs r := by
  let p := arun k s (lift (loadWord src negate))
  let q := arun k p LeanCompCert.Ports.Section413SignedScale.body
  have hp : p.regs r = s.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k r
      (lift (loadWord src negate)) hload s
  have hq : q.regs r = p.regs r :=
    LeanCompCert.Verified.ArrayRegFrame.arun_frame k r
      LeanCompCert.Ports.Section413SignedScale.body hscale p
  rw [oneStage, arun_append, arun_append, arun_lift]
  change srun k q.regs
    [.mov dest (.reg LeanCompCert.Ports.Section413SignedScale.rOut)] r = _
  rw [srun_untouched]
  · exact hq.trans hp
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    simpa only [sdest] using hdest

theorem oneStage_inLo_frame (k : Nat) (s : AState) (src dest : Nat)
    (negate : Bool) (hdest : dest ≠ rInLo) :
    (arun k s (oneStage src dest negate)).regs rInLo = s.regs rInLo := by
  apply oneStage_frame_of k rInLo s src dest negate
  · cases negate <;>
      simp [lift, loadWord,
        LeanCompCert.Ports.Section413WindowCellDiv.loadWord,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, rInLo,
        LeanCompCert.Ports.Section413WindowCellDiv.rInLo,
        LeanCompCert.Ports.Section413SignedDiv.rDiv,
        LeanCompCert.Ports.Section413SignedDiv.rWord]
  · decide
  · exact hdest

theorem oneStage_inHi_frame (k : Nat) (s : AState) (src dest : Nat)
    (negate : Bool) (hdest : dest ≠ rInHi) :
    (arun k s (oneStage src dest negate)).regs rInHi = s.regs rInHi := by
  apply oneStage_frame_of k rInHi s src dest negate
  · cases negate <;>
      simp [lift, loadWord,
        LeanCompCert.Ports.Section413WindowCellDiv.loadWord,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, rInHi,
        LeanCompCert.Ports.Section413WindowCellDiv.rInHi,
        LeanCompCert.Ports.Section413SignedDiv.rDiv,
        LeanCompCert.Ports.Section413SignedDiv.rWord]
  · decide
  · exact hdest

theorem oneStage_gate_frame (k : Nat) (s : AState) (src dest : Nat)
    (negate : Bool) (hdest : dest ≠ rGate) :
    (arun k s (oneStage src dest negate)).regs rGate = s.regs rGate := by
  apply oneStage_frame_of k rGate s src dest negate
  · cases negate <;>
      simp [lift, loadWord,
        LeanCompCert.Ports.Section413WindowCellDiv.loadWord,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, rGate,
        LeanCompCert.Ports.Section413WindowCellDiv.rGate,
        LeanCompCert.Ports.Section413SignedDiv.rDiv,
        LeanCompCert.Ports.Section413SignedDiv.rWord]
  · decide
  · exact hdest

theorem oneStage_outLo_frame (k : Nat) (s : AState) (src dest : Nat)
    (negate : Bool) (hdest : dest ≠ rOutLo) :
    (arun k s (oneStage src dest negate)).regs rOutLo = s.regs rOutLo := by
  apply oneStage_frame_of k rOutLo s src dest negate
  · cases negate <;>
      simp [lift, loadWord,
        LeanCompCert.Ports.Section413WindowCellDiv.loadWord,
        LeanCompCert.Verified.ArrayRegFrame.writes,
        LeanCompCert.Verified.ArrayRegFrame.instrWrites, rOutLo,
        LeanCompCert.Ports.Section413WindowCellDiv.rOutLo,
        LeanCompCert.Ports.Section413SignedDiv.rDiv,
        LeanCompCert.Ports.Section413SignedDiv.rWord]
  · decide
  · exact hdest

theorem gateStage_outputs (k : Nat) (s : AState) :
    let out := arun k s (lift gateStage)
    out.regs rOutLo = (s.regs rOutLo * s.regs rGate) % M ∧
      out.regs rOutHi = (s.regs rOutHi * s.regs rGate) % M ∧
      out.arr = s.arr := by
  dsimp only
  rw [arun_lift]
  simp [gateStage, srun, sdest, sval, denoteOperand, denoteOp,
    RegState.set, rOutLo, rOutHi, rGate,
    LeanCompCert.Ports.Section413WindowCellDiv.rOutLo,
    LeanCompCert.Ports.Section413WindowCellDiv.rOutHi,
    LeanCompCert.Ports.Section413WindowCellDiv.rGate]

/-- The two compiled checked multiplications compute both signed endpoints,
then apply the event gate.  The hypotheses are compact receipts for the two
constant-size multiplier invocations; the production event fold is not
evaluated by Lean. -/
theorem body_clean_outputs (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hcleanLo :
      (arun k
        (arun k s (lift (loadWord
          (if negate then rInHi else rInLo) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0)
    (hcleanHi :
      let p := arun k s
        (oneStage (if negate then rInHi else rInLo) rOutLo negate)
      (arun k
        (arun k p (lift (loadWord
          (if negate then rInLo else rInHi) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0) :
    let out := arun k s (body negate)
    out.regs rOutLo =
        (encodeZ ((s.regs rFactor : Int) *
          decodeZ (if negate then
            LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInHi)
          else s.regs rInLo)) * s.regs rGate) % M ∧
      out.regs rOutHi =
        (encodeZ ((s.regs rFactor : Int) *
          decodeZ (if negate then
            LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInLo)
          else s.regs rInHi)) * s.regs rGate) % M ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s
    (oneStage (if negate then rInHi else rInLo) rOutLo negate)
  let q := arun k p
    (oneStage (if negate then rInLo else rInHi) rOutHi negate)
  have hlow := oneStage_clean_output k s
    (if negate then rInHi else rInLo) rOutLo negate
    (by cases negate <;> decide) hword harray hcleanLo
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpFactor : p.regs rFactor = s.regs rFactor := by
    exact oneStage_factor_frame k s
      (if negate then rInHi else rInLo) rOutLo negate (by decide)
  have hpInLo : p.regs rInLo = s.regs rInLo := by
    exact oneStage_inLo_frame k s
      (if negate then rInHi else rInLo) rOutLo negate (by decide)
  have hpInHi : p.regs rInHi = s.regs rInHi := by
    exact oneStage_inHi_frame k s
      (if negate then rInHi else rInLo) rOutLo negate (by decide)
  have hpGate : p.regs rGate = s.regs rGate := by
    exact oneStage_gate_frame k s
      (if negate then rInHi else rInLo) rOutLo negate (by decide)
  have hhigh := oneStage_clean_output k p
    (if negate then rInLo else rInHi) rOutHi negate
    (by cases negate <;> decide) hpword hparray (by
      simpa only [p] using hcleanHi)
  have hqOutLo : q.regs rOutLo = p.regs rOutLo := by
    exact oneStage_outLo_frame k p
      (if negate then rInLo else rInHi) rOutHi negate (by decide)
  have hqGate : q.regs rGate = s.regs rGate := by
    rw [oneStage_gate_frame k p
      (if negate then rInLo else rInHi) rOutHi negate (by decide), hpGate]
  have hqLo : q.regs rOutLo =
      encodeZ ((s.regs rFactor : Int) *
        decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInHi)
        else s.regs rInLo)) := by
    apply hqOutLo.trans
    dsimp only [p]
    cases hneg : negate
    · simpa only [hneg, Bool.false_eq_true, if_false] using hlow.1
    · simpa only [hneg, if_true] using hlow.1
  have hqHi : q.regs rOutHi =
      encodeZ ((s.regs rFactor : Int) *
        decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInLo)
        else s.regs rInHi)) := by
    dsimp only [q]
    cases hneg : negate
    · simpa only [hneg, Bool.false_eq_true, if_false, hpFactor, hpInHi]
        using hhigh.1
    · simpa only [hneg, if_true, hpFactor, hpInLo] using hhigh.1
  have hqarr : q.arr = s.arr := hhigh.2.trans hlow.2
  rw [body, arun_append, arun_append]
  have hgate := gateStage_outputs k q
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hqLo, hqGate] using hgate.1
  · simpa only [hqHi, hqGate] using hgate.2.1
  · exact hgate.2.2.trans hqarr

theorem body_clean_outputs_gate_one (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hcleanLo :
      (arun k
        (arun k s (lift (loadWord
          (if negate then rInHi else rInLo) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0)
    (hcleanHi :
      let p := arun k s
        (oneStage (if negate then rInHi else rInLo) rOutLo negate)
      (arun k
        (arun k p (lift (loadWord
          (if negate then rInLo else rInHi) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0)
    (hgate : s.regs rGate = 1) :
    let out := arun k s (body negate)
    out.regs rOutLo = encodeZ ((s.regs rFactor : Int) *
        decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInHi)
        else s.regs rInLo)) ∧
      out.regs rOutHi = encodeZ ((s.regs rFactor : Int) *
        decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInLo)
        else s.regs rInHi)) ∧
      out.arr = s.arr := by
  dsimp only
  have h := body_clean_outputs k s negate hword harray hcleanLo hcleanHi
  refine ⟨?_, ?_, h.2.2⟩
  · rw [h.1, hgate, Nat.mul_one,
      Nat.mod_eq_of_lt
        (LeanCompCert.Ports.Section413G1Sound.encodeZ_lt_M _)]
  · rw [h.2.1, hgate, Nat.mul_one,
      Nat.mod_eq_of_lt
        (LeanCompCert.Ports.Section413G1Sound.encodeZ_lt_M _)]

theorem body_clean_outputs_gate_zero (k : Nat) (s : AState) (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hcleanLo :
      (arun k
        (arun k s (lift (loadWord
          (if negate then rInHi else rInLo) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0)
    (hcleanHi :
      let p := arun k s
        (oneStage (if negate then rInHi else rInLo) rOutLo negate)
      (arun k
        (arun k p (lift (loadWord
          (if negate then rInLo else rInHi) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0)
    (hgate : s.regs rGate = 0) :
    let out := arun k s (body negate)
    out.regs rOutLo = 0 ∧ out.regs rOutHi = 0 ∧ out.arr = s.arr := by
  dsimp only
  have h := body_clean_outputs k s negate hword harray hcleanLo hcleanHi
  rw [h.1, h.2.1, hgate, Nat.mul_zero, Nat.zero_mod]
  exact ⟨rfl, rfl, h.2.2⟩

theorem body_clean_outputs_gate_one_decoded (k : Nat) (s : AState)
    (negate : Bool)
    (hword : ∀ j, s.regs j < M) (harray : ∀ j, s.arr j < M)
    (hcleanLo :
      (arun k
        (arun k s (lift (loadWord
          (if negate then rInHi else rInLo) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0)
    (hcleanHi :
      let p := arun k s
        (oneStage (if negate then rInHi else rInLo) rOutLo negate)
      (arun k
        (arun k p (lift (loadWord
          (if negate then rInLo else rInHi) negate)))
        LeanCompCert.Ports.Section413SignedScale.body).regs
          LeanCompCert.Ports.Section413SignedScale.rViol = 0)
    (hgate : s.regs rGate = 1) :
    let out := arun k s (body negate)
    decodeZ (out.regs rOutLo) = (s.regs rFactor : Int) *
        decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInHi)
        else s.regs rInLo) ∧
      decodeZ (out.regs rOutHi) = (s.regs rFactor : Int) *
        decodeZ (if negate then
          LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInLo)
        else s.regs rInHi) ∧
      out.arr = s.arr := by
  dsimp only
  let p := arun k s
    (oneStage (if negate then rInHi else rInLo) rOutLo negate)
  have henc := body_clean_outputs_gate_one k s negate hword harray
    hcleanLo hcleanHi hgate
  have hlo := oneStage_clean_output_range k s
    (if negate then rInHi else rInLo) rOutLo negate
    (by cases negate <;> decide) hword harray hcleanLo
  have hpword : ∀ j, p.regs j < M := arun_regs_word k _ _ hword harray
  have hparray : ∀ j, p.arr j < M := arun_arr_word k _ _ hword harray
  have hpFactor : p.regs rFactor = s.regs rFactor := by
    exact oneStage_factor_frame k s
      (if negate then rInHi else rInLo) rOutLo negate (by decide)
  have hpInLo : p.regs rInLo = s.regs rInLo := by
    exact oneStage_inLo_frame k s
      (if negate then rInHi else rInLo) rOutLo negate (by decide)
  have hpInHi : p.regs rInHi = s.regs rInHi := by
    exact oneStage_inHi_frame k s
      (if negate then rInHi else rInLo) rOutLo negate (by decide)
  have hhi := oneStage_clean_output_range k p
    (if negate then rInLo else rInHi) rOutHi negate
    (by cases negate <;> decide) hpword hparray
    (by simpa only [p] using hcleanHi)
  have hloLower : -(H63 : Int) ≤ (s.regs rFactor : Int) *
      decodeZ (if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInHi)
      else s.regs rInLo) := by
    cases hneg : negate
    · simpa only [hneg, Bool.false_eq_true, if_false] using hlo.2.1
    · simpa only [hneg, if_true] using hlo.2.1
  have hloUpper : (s.regs rFactor : Int) *
      decodeZ (if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInHi)
      else s.regs rInLo) < (H63 : Int) := by
    cases hneg : negate
    · simpa only [hneg, Bool.false_eq_true, if_false] using hlo.2.2.1
    · simpa only [hneg, if_true] using hlo.2.2.1
  have hhiLower : -(H63 : Int) ≤ (s.regs rFactor : Int) *
      decodeZ (if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInLo)
      else s.regs rInHi) := by
    cases hneg : negate
    · simpa only [hneg, Bool.false_eq_true, if_false, hpFactor, hpInHi]
        using hhi.2.1
    · simpa only [hneg, if_true, hpFactor, hpInLo] using hhi.2.1
  have hhiUpper : (s.regs rFactor : Int) *
      decodeZ (if negate then
        LeanCompCert.Ports.Section413G1Program.tsub 0 (s.regs rInLo)
      else s.regs rInHi) < (H63 : Int) := by
    cases hneg : negate
    · simpa only [hneg, Bool.false_eq_true, if_false, hpFactor, hpInHi]
        using hhi.2.2.1
    · simpa only [hneg, if_true, hpFactor, hpInLo] using hhi.2.2.1
  refine ⟨?_, ?_, henc.2.2⟩
  · rw [henc.1, decodeZ_encodeZ _ hloLower hloUpper]
  · rw [henc.2.1, decodeZ_encodeZ _ hhiLower hhiUpper]

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
#print axioms body_clean_outputs
#print axioms body_clean_outputs_gate_one
#print axioms body_clean_outputs_gate_zero
#print axioms body_clean_outputs_gate_one_decoded
#print axioms program_wf

end LeanCompCert.Ports.Section413WindowCellScale

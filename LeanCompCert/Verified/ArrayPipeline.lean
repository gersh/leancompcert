import LeanCompCert.Verified.ArrayBridge
import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Sequential array-program pipelines

`AProgram.denote` starts from a zero array, which is right for a standalone
artifact but not for a sequence of compiled loops sharing one caller-owned
array.  This module gives the same verified compiler simulation from an
arbitrary represented input array.  Each stage resets its scalar locals, just
as a fresh emitted C function does, while retaining the predecessor's memory.
-/

namespace LeanCompCert.Verified.ArrayState

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Verified.ArrayFoldBridge

private theorem mbind_some {α β : Type} (a : α) (f : α → Option β) :
    ((some a : Option α) >>= f) = f a := rfl

def initialAStateWithArray (arr : Nat → Nat) : AState :=
  { regs := initialState, arr := arr }

def AProgram.runFromArray (p : AProgram) (arr : Nat → Nat) : Option AState := do
  let s ← denoteAInstrs p.arrayLen 0 (initialAStateWithArray arr) p.init
  let s ← (List.range p.loopCount).foldlM
    (fun s index => denoteAInstrs p.arrayLen index s p.body) s
  denoteAInstrs p.arrayLen 0 s p.epilogue

def AProgram.initialMCCWithMem (p : AProgram) (base : Int) (mem : Mem) : MCCState :=
  { env := (p.initialMCC base).env, mem := mem }

/-- Symbolic source execution from an arbitrary array.  The loop remains a
pure mathematical fold; this theorem never asks Lean to reduce that fold. -/
theorem AProgram.runFromArray_eq_foldl_mem
    (p : AProgram) (P : AState → Prop) (step : Nat → AState → AState)
    (fin : AState → AState) (arr : Nat → Nat) (s₀ : AState)
    (hInit : denoteAInstrs p.arrayLen 0 (initialAStateWithArray arr) p.init = some s₀)
    (hP₀ : P s₀)
    (hStep : ∀ index s, index < p.loopCount → P s →
      denoteAInstrs p.arrayLen index s p.body = some (step index s))
    (hClosed : ∀ index s, index < p.loopCount → P s → P (step index s))
    (hEpilogue : ∀ s, P s →
      denoteAInstrs p.arrayLen 0 s p.epilogue = some (fin s)) :
    p.runFromArray arr = some
      (fin ((List.range p.loopCount).foldl
        (fun s index => step index s) s₀)) := by
  have hmem : ∀ i ∈ List.range p.loopCount, i < p.loopCount :=
    fun i hi => List.mem_range.mp hi
  have hFoldP : P ((List.range p.loopCount).foldl
      (fun s index => step index s) s₀) :=
    foldl_closed_mem (fun i => i < p.loopCount) P step hClosed
      (List.range p.loopCount) hmem s₀ hP₀
  unfold AProgram.runFromArray
  rw [hInit]
  simp only [mbind_some]
  rw [foldlM_abody_eq_foldl_mem p.arrayLen p.body
    (fun i => i < p.loopCount) P step hStep hClosed
    (List.range p.loopCount) hmem s₀ hP₀]
  simp only [mbind_some]
  exact hEpilogue _ hFoldP

/-- The ordinary array compiler theorem with an arbitrary represented input
array.  It returns the complete final simulation relation, so a following
stage can consume the resulting memory without materialising it in Lean. -/
theorem AProgram.evalCC_compile_fromArray (p : AProgram) (hWF : p.WF)
    (base : Int) (hBase : BaseOk p.arrayLen base)
    (arr : Nat → Nat) (mem : Mem)
    (hCells : ∀ k, k < p.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < p.arrayLen → arr k < M)
    (out : AState) (hRun : p.runFromArray arr = some out) :
    ∃ m, evalMCCSequence (p.initialMCCWithMem base mem) p.compile = some m ∧
      ARel p.regCount p.arrayLen base out m := by
  obtain ⟨_, hInit, hBody, hEpilogue⟩ := hWF
  obtain ⟨env0, hPre, hInv0, hbase0⟩ := apreamble_correct p base
  let s0 := initialAStateWithArray arr
  let m0 : MCCState := { env := env0, mem := mem }
  have hRel0 : ARel p.regCount p.arrayLen base s0 m0 := by
    exact ⟨hInv0, hbase0, hCells, hCellsLt⟩
  unfold AProgram.compile
  rw [List.append_assoc, List.append_assoc, evalMCCSequence_append]
  rw [show evalMCCSequence (p.initialMCCWithMem base mem)
      (apreamble p.regCount) = some m0 from by
    unfold AProgram.initialMCCWithMem apreamble m0
    rw [evalMCCSequence_straight, hPre]
    rfl]
  simp only [Option.bind_some]
  rw [evalMCCSequence_append]
  unfold AProgram.runFromArray at hRun
  have hInitStep := compileAInstrs_correct (index := 0) hBase p.init hInit
    s0 m0 hRel0
  cases hInitD : denoteAInstrs p.arrayLen 0 s0 p.init with
  | none => rw [hInitD] at hRun; contradiction
  | some s1 =>
      rw [hInitD] at hInitStep hRun
      cases hInitE : evalMCCSequence m0
          (compileAInstrs p.regCount 0 p.init) with
      | none => rw [hInitE] at hInitStep; exact hInitStep.elim
      | some m1 =>
          rw [hInitE] at hInitStep
          simp only [Option.bind_some, mbind_some] at hRun ⊢
          rw [evalMCCSequence_append]
          have hFoldStep := foldBodyA_correct hBase p.body hBody
            (List.range p.loopCount) s1 m1 hInitStep
          rw [show evalMCCSequence m1
              (foldTraceM p.loopCount
                (fun index => compileAInstrs p.regCount index p.body)) =
              (List.range p.loopCount).foldlM
                (fun m index => evalMCCSequence m
                  (compileAInstrs p.regCount index p.body)) m1 from
            evalMCCSequence_flatMap _ _ _]
          cases hFoldD : (List.range p.loopCount).foldlM
              (fun s index => denoteAInstrs p.arrayLen index s p.body) s1 with
          | none => rw [hFoldD] at hRun; contradiction
          | some s2 =>
              rw [hFoldD] at hFoldStep hRun
              cases hFoldE : (List.range p.loopCount).foldlM
                  (fun m index => evalMCCSequence m
                    (compileAInstrs p.regCount index p.body)) m1 with
              | none => rw [hFoldE] at hFoldStep; exact hFoldStep.elim
              | some m2 =>
                  rw [hFoldE] at hFoldStep
                  simp only [Option.bind_some, mbind_some] at hRun ⊢
                  have hEpiStep := compileAInstrs_correct (index := 0) hBase
                    p.epilogue hEpilogue s2 m2 hFoldStep
                  cases hEpiD : denoteAInstrs p.arrayLen 0 s2 p.epilogue with
                  | none => rw [hEpiD] at hRun; contradiction
                  | some s3 =>
                      rw [hEpiD] at hEpiStep hRun
                      cases hEpiE : evalMCCSequence m2
                          (compileAInstrs p.regCount 0 p.epilogue) with
                      | none => rw [hEpiE] at hEpiStep; exact hEpiStep.elim
                      | some m3 =>
                          rw [hEpiE] at hEpiStep
                          have hs : s3 = out := by simpa using hRun
                          subst out
                          exact ⟨m3, rfl, hEpiStep⟩

/-- Two fresh-local compiled functions compose through their shared array.
The theorem deliberately exposes both CCIR executions, matching a C driver
that calls the two emitted functions on the same base pointer. -/
theorem AProgram.evalCC_compile_fromArray_two
    (p q : AProgram) (hpWF : p.WF) (hqWF : q.WF)
    (hLen : q.arrayLen = p.arrayLen)
    (base : Int) (hBase : BaseOk p.arrayLen base)
    (arr : Nat → Nat) (mem : Mem)
    (hCells : ∀ k, k < p.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < p.arrayLen → arr k < M)
    (mid out : AState)
    (hpRun : p.runFromArray arr = some mid)
    (hqRun : q.runFromArray mid.arr = some out) :
    ∃ mp mq,
      evalMCCSequence (p.initialMCCWithMem base mem) p.compile = some mp ∧
      evalMCCSequence (q.initialMCCWithMem base mp.mem) q.compile = some mq ∧
      ARel q.regCount q.arrayLen base out mq := by
  obtain ⟨mp, hpEval, hpRel⟩ :=
    p.evalCC_compile_fromArray hpWF base hBase arr mem hCells hCellsLt mid hpRun
  have hqBase : BaseOk q.arrayLen base := by simpa [hLen] using hBase
  have hqCells : ∀ k, k < q.arrayLen →
      mp.mem (cellAddr base k) = some (((mid.arr k : Nat) : Int)) := by
    intro k hk
    exact hpRel.hcells k (by simpa [hLen] using hk)
  have hqCellsLt : ∀ k, k < q.arrayLen → mid.arr k < M := by
    intro k hk
    exact hpRel.hcellsLt k (by simpa [hLen] using hk)
  obtain ⟨mq, hqEval, hqRel⟩ :=
    q.evalCC_compile_fromArray hqWF base hqBase mid.arr mp.mem
      hqCells hqCellsLt out hqRun
  exact ⟨mp, mq, hpEval, hqEval, hqRel⟩

theorem AProgram.evalCC_compile_fromArray_three
    (p q r : AProgram) (hpWF : p.WF) (hqWF : q.WF) (hrWF : r.WF)
    (hqLen : q.arrayLen = p.arrayLen) (hrLen : r.arrayLen = p.arrayLen)
    (base : Int) (hBase : BaseOk p.arrayLen base)
    (arr : Nat → Nat) (mem : Mem)
    (hCells : ∀ k, k < p.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < p.arrayLen → arr k < M)
    (mid₁ mid₂ out : AState)
    (hpRun : p.runFromArray arr = some mid₁)
    (hqRun : q.runFromArray mid₁.arr = some mid₂)
    (hrRun : r.runFromArray mid₂.arr = some out) :
    ∃ mp mq mr,
      evalMCCSequence (p.initialMCCWithMem base mem) p.compile = some mp ∧
      evalMCCSequence (q.initialMCCWithMem base mp.mem) q.compile = some mq ∧
      evalMCCSequence (r.initialMCCWithMem base mq.mem) r.compile = some mr ∧
      ARel r.regCount r.arrayLen base out mr := by
  obtain ⟨mp, mq, hpEval, hqEval, hqRel⟩ :=
    p.evalCC_compile_fromArray_two q hpWF hqWF hqLen base hBase arr mem
      hCells hCellsLt mid₁ mid₂ hpRun hqRun
  have hrBase : BaseOk r.arrayLen base := by simpa [hrLen] using hBase
  have hrCells : ∀ k, k < r.arrayLen →
      mq.mem (cellAddr base k) = some (((mid₂.arr k : Nat) : Int)) := by
    intro k hk
    exact hqRel.hcells k (by simpa [hqLen, hrLen] using hk)
  have hrCellsLt : ∀ k, k < r.arrayLen → mid₂.arr k < M := by
    intro k hk
    exact hqRel.hcellsLt k (by simpa [hqLen, hrLen] using hk)
  obtain ⟨mr, hrEval, hrRel⟩ :=
    r.evalCC_compile_fromArray hrWF base hrBase mid₂.arr mq.mem
      hrCells hrCellsLt out hrRun
  exact ⟨mp, mq, mr, hpEval, hqEval, hrEval, hrRel⟩

#print axioms AProgram.evalCC_compile_fromArray
#print axioms AProgram.runFromArray_eq_foldl_mem
#print axioms AProgram.evalCC_compile_fromArray_two
#print axioms AProgram.evalCC_compile_fromArray_three

end LeanCompCert.Verified.ArrayState

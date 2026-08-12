import LeanCompCert.Verified.ArrayBridge

/-!
# Final-state form of the array compiler bridge

This leaf module exposes the final source/CCIR relation without making every
array-program development rebuild when the state-level interface changes.
-/

namespace LeanCompCert.Verified.ArrayState

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.MemFragment

private theorem obind_some {α β : Type _} (a : α) (f : α → Option β) :
    Option.bind (some a) f = f a := rfl

private theorem mbind_some {α β : Type _} (a : α) (f : α → Option β) :
    ((some a : Option α) >>= f) = f a := rfl

/-- State-level form of the array reflection bridge.  Besides successful
execution, it exposes the three source states and the final `ARel`, so a
certificate may soundly compare compiled memory observations with cells
written by the source epilogue. -/
theorem AProgram.evalCC_compile_finalRel (p : AProgram) (hWF : p.WF)
    (base : Int) (hBase : BaseOk p.arrayLen base) (n : Nat)
    (hDenote : p.denote = some n) :
    ∃ s1 s2 s3 m3,
      denoteAInstrs p.arrayLen 0 initialAState p.init = some s1 ∧
      (List.range p.loopCount).foldlM
          (fun s index => denoteAInstrs p.arrayLen index s p.body) s1 =
        some s2 ∧
      denoteAInstrs p.arrayLen 0 s2 p.epilogue = some s3 ∧
      evalMCCSequence (p.initialMCC base) p.compile = some m3 ∧
      ARel p.regCount p.arrayLen base s3 m3 := by
  obtain ⟨_hOutput, hInit, hBody, hEpilogue⟩ := hWF
  obtain ⟨env0, hPre, hInv0, hbase0⟩ := apreamble_correct p base
  have hRel0 : ARel p.regCount p.arrayLen base initialAState
      { env := env0, mem := (p.initialMCC base).mem } := by
    refine ⟨hInv0, hbase0, ?_, ?_⟩
    · intro k hk
      show initialMem p.arrayLen base (cellAddr base k) =
        some ((0 : Nat) : Int)
      rw [initialMem_cell p.arrayLen base hk]
      rfl
    · intro k _; exact M_pos
  unfold AProgram.denote at hDenote
  have hTrace : evalMCCSequence (p.initialMCC base) p.compile =
      Option.bind
        (evalMCCSequence
          { env := env0, mem := (p.initialMCC base).mem }
          (compileAInstrs p.regCount 0 p.init))
        (fun m1 => Option.bind
          ((List.range p.loopCount).foldlM
            (fun m index => evalMCCSequence m
              (compileAInstrs p.regCount index p.body)) m1)
          (fun m2 => evalMCCSequence m2
            (compileAInstrs p.regCount 0 p.epilogue))) := by
    unfold AProgram.compile
    rw [List.append_assoc, List.append_assoc, evalMCCSequence_append]
    rw [show evalMCCSequence (p.initialMCC base) (apreamble p.regCount) =
        some { env := env0, mem := (p.initialMCC base).mem } from by
      unfold apreamble
      rw [evalMCCSequence_straight, hPre]
      rfl]
    simp only [obind_some]
    rw [evalMCCSequence_append]
    congr 1
    funext m1
    rw [evalMCCSequence_append]
    rw [show evalMCCSequence m1
        (foldTraceM p.loopCount
          (fun index => compileAInstrs p.regCount index p.body)) =
        (List.range p.loopCount).foldlM
          (fun m index => evalMCCSequence m
            (compileAInstrs p.regCount index p.body)) m1 from
      evalMCCSequence_flatMap _ _ _]
  cases hInitD : denoteAInstrs p.arrayLen 0 initialAState p.init with
  | none => rw [hInitD] at hDenote; exact absurd hDenote (by simp)
  | some s1 =>
      have hInitStep := compileAInstrs_correct (index := 0) hBase p.init hInit
        initialAState _ hRel0
      rw [hInitD] at hInitStep hDenote
      cases hInitE : evalMCCSequence
          { env := env0, mem := (p.initialMCC base).mem }
          (compileAInstrs p.regCount 0 p.init) with
      | none => rw [hInitE] at hInitStep; exact hInitStep.elim
      | some m1 =>
          rw [hInitE] at hInitStep
          simp only [mbind_some] at hDenote
          have hFoldStep := foldBodyA_correct hBase p.body hBody
            (List.range p.loopCount) s1 m1 hInitStep
          cases hFoldD : (List.range p.loopCount).foldlM
              (fun s index => denoteAInstrs p.arrayLen index s p.body) s1 with
          | none => rw [hFoldD] at hDenote; exact absurd hDenote (by simp)
          | some s2 =>
              rw [hFoldD] at hFoldStep hDenote
              cases hFoldE : (List.range p.loopCount).foldlM
                  (fun m index => evalMCCSequence m
                    (compileAInstrs p.regCount index p.body)) m1 with
              | none => rw [hFoldE] at hFoldStep; exact hFoldStep.elim
              | some m2 =>
                  rw [hFoldE] at hFoldStep
                  simp only [mbind_some] at hDenote
                  have hEpiStep := compileAInstrs_correct (index := 0) hBase
                    p.epilogue hEpilogue s2 m2 hFoldStep
                  cases hEpiD : denoteAInstrs p.arrayLen 0 s2 p.epilogue with
                  | none => rw [hEpiD] at hDenote; exact absurd hDenote (by simp)
                  | some s3 =>
                      rw [hEpiD] at hEpiStep hDenote
                      cases hEpiE : evalMCCSequence m2
                          (compileAInstrs p.regCount 0 p.epilogue) with
                      | none => rw [hEpiE] at hEpiStep; exact hEpiStep.elim
                      | some m3 =>
                          rw [hEpiE] at hEpiStep
                          refine ⟨s1, s2, s3, m3, rfl, hFoldD, hEpiD, ?_,
                            hEpiStep⟩
                          simp [hTrace, hInitE, hFoldE, hEpiE]

end LeanCompCert.Verified.ArrayState

import LeanCompCert.Verified.ArrayAudit
import LeanCompCert.Verified.ArrayRolledPipeline

/-!
# Fail-safe audits from caller-owned arrays

`ArrayAudit` proves totality and zero-soundness for a standalone program whose
array is initially zero.  Compiled producer/consumer pipelines instead start
each fresh function with zero scalar locals and the predecessor's array.  The
theorems here lift the same audit argument to `AProgram.runFromArray`.

The loop count remains symbolic throughout.  A physical zero receipt for the
rolled audited program therefore establishes source definedness without Lean
executing the production fold.
-/

namespace LeanCompCert.Verified.ArrayAudit

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment

theorem initialAStateWithArray_word (arr : Nat → Nat)
    (harr : ∀ j, arr j < M) : WordState (initialAStateWithArray arr) := by
  constructor
  · intro j
    simp [initialAStateWithArray, initialState, M]
  · exact harr

theorem arunFold_word (body : List AInstr) (indices : List Nat)
    (s : AState) (hs : WordState s) :
    WordState (indices.foldl (fun st k => arun k st body) s) := by
  induction indices generalizing s with
  | nil => exact hs
  | cons k rest ih =>
      apply ih
      exact arun_word k body s hs.1 hs.2

/-- Every successful partial execution from a word array ends in a word
state.  This is useful at pipeline seams independently of auditing. -/
theorem AProgram.runFromArray_word (p : AProgram) (arr : Nat → Nat)
    (harr : ∀ j, arr j < M) (out : AState)
    (hRun : p.runFromArray arr = some out) : WordState out := by
  unfold AProgram.runFromArray at hRun
  cases hinit : denoteAInstrs p.arrayLen 0 (initialAStateWithArray arr) p.init with
  | none => simp [hinit] at hRun
  | some entry =>
      rw [hinit] at hRun
      change ((List.range p.loopCount).foldlM
          (fun s index => denoteAInstrs p.arrayLen index s p.body) entry).bind
          (fun s => denoteAInstrs p.arrayLen 0 s p.epilogue) = some out at hRun
      cases hloop : (List.range p.loopCount).foldlM
          (fun s index => denoteAInstrs p.arrayLen index s p.body) entry with
      | none => simp [hloop] at hRun
      | some loopOut =>
          rw [hloop] at hRun
          cases hepi : denoteAInstrs p.arrayLen 0 loopOut p.epilogue with
          | none => simp [hepi] at hRun
          | some final =>
              simp only [Option.bind_some] at hRun
              have hentry : entry = arun 0 (initialAStateWithArray arr) p.init :=
                eq_arun_of_denoteAInstrs_eq_some p.arrayLen 0 p.init
                  (initialAStateWithArray arr) entry hinit
              have hloopOut : loopOut = (List.range p.loopCount).foldl
                  (fun s index => arun index s p.body) entry :=
                eq_foldl_arun_of_foldlM_denote_eq_some p.arrayLen p.body
                  (List.range p.loopCount) entry loopOut hloop
              have hfinal : final = arun 0 loopOut p.epilogue :=
                eq_arun_of_denoteAInstrs_eq_some p.arrayLen 0 p.epilogue
                  loopOut final hepi
              have hstart := initialAStateWithArray_word arr harr
              have hentryWord : WordState entry := by
                rw [hentry]
                exact arun_word 0 p.init (initialAStateWithArray arr)
                  hstart.1 hstart.2
              have hloopWord : WordState loopOut := by
                rw [hloopOut]
                exact arunFold_word p.body (List.range p.loopCount) entry
                  hentryWord
              have hfinalWord : WordState final := by
                rw [hfinal]
                exact arun_word 0 p.epilogue loopOut hloopWord.1 hloopWord.2
              rw [hepi] at hRun
              simp only [Option.some.injEq] at hRun
              subst out
              exact hfinalWord

/-- The guarded program has a successful source execution from every
machine-word input array. -/
theorem auditProgram_runFromArray (p : AProgram) (hp : p.WF)
    (arr : Nat → Nat) (harr : ∀ j, arr j < M)
    (hlen : 0 < p.arrayLen) (hlenM : p.arrayLen < M) :
    let entry := arun 0 (initialAStateWithArray arr)
      (auditBlock p.arrayLen p.regCount p.init)
    let loopOut := (List.range p.loopCount).foldl
      (fun s idx => arun idx s
        (auditBlock p.arrayLen p.regCount p.body)) entry
    (auditProgram p).runFromArray arr = some
      (arun 0 loopOut
        (auditBlock p.arrayLen p.regCount p.epilogue)) := by
  let entry := arun 0 (initialAStateWithArray arr)
    (auditBlock p.arrayLen p.regCount p.init)
  let step := fun idx s =>
    arun idx s (auditBlock p.arrayLen p.regCount p.body)
  let fin := fun s =>
    arun 0 s (auditBlock p.arrayLen p.regCount p.epilogue)
  have hzero := initialAStateWithArray_word arr harr
  have hInit := auditBlock_denote_arun p.arrayLen p.regCount 0 p.init
    (initialAStateWithArray arr) hp.2.1 hlen hlenM hzero.1 hzero.2
  have hP0 : WordState entry :=
    arun_word 0 (auditBlock p.arrayLen p.regCount p.init)
      (initialAStateWithArray arr) hzero.1 hzero.2
  have hStep : ∀ idx s, idx < (auditProgram p).loopCount → WordState s →
      denoteAInstrs (auditProgram p).arrayLen idx s (auditProgram p).body =
        some (step idx s) := by
    intro idx s _ hs
    exact auditBlock_denote_arun p.arrayLen p.regCount idx p.body s
      hp.2.2.1 hlen hlenM hs.1 hs.2
  have hClosed : ∀ idx s, idx < (auditProgram p).loopCount → WordState s →
      WordState (step idx s) := by
    intro idx s _ hs
    exact arun_word idx (auditBlock p.arrayLen p.regCount p.body) s hs.1 hs.2
  have hEpi : ∀ s, WordState s →
      denoteAInstrs (auditProgram p).arrayLen 0 s (auditProgram p).epilogue =
        some (fin s) := by
    intro s hs
    exact auditBlock_denote_arun p.arrayLen p.regCount 0 p.epilogue s
      hp.2.2.2 hlen hlenM hs.1 hs.2
  simpa only [auditProgram, entry, step, fin] using
    AProgram.runFromArray_eq_foldl_mem (auditProgram p) WordState step fin
      arr entry hInit hP0 hStep hClosed hEpi

/-- A zero final audit recovers the original partial execution from the same
caller-owned array and relates every source-visible output location. -/
theorem auditProgram_zero_sound_fromArray (p : AProgram) (hp : p.WF)
    (arr : Nat → Nat) (harr : ∀ j, arr j < M)
    (hlen : 0 < p.arrayLen) (hlenM : p.arrayLen < M) :
    let aEntry := arun 0 (initialAStateWithArray arr)
      (auditBlock p.arrayLen p.regCount p.init)
    let aLoop := (List.range p.loopCount).foldl (fun s idx =>
      arun idx s (auditBlock p.arrayLen p.regCount p.body)) aEntry
    let aFinal := arun 0 aLoop
      (auditBlock p.arrayLen p.regCount p.epilogue)
    let sEntry := arun 0 (initialAStateWithArray arr) p.init
    let sLoop := (List.range p.loopCount).foldl
      (fun s idx => arun idx s p.body) sEntry
    let sFinal := arun 0 sLoop p.epilogue
    aFinal.regs (auditReg p.regCount) = 0 →
      p.runFromArray arr = some sFinal ∧
        SourceAgree p.regCount aFinal sFinal := by
  let aEntry := arun 0 (initialAStateWithArray arr)
    (auditBlock p.arrayLen p.regCount p.init)
  let aLoop := (List.range p.loopCount).foldl (fun s idx =>
    arun idx s (auditBlock p.arrayLen p.regCount p.body)) aEntry
  let aFinal := arun 0 aLoop
    (auditBlock p.arrayLen p.regCount p.epilogue)
  let sEntry := arun 0 (initialAStateWithArray arr) p.init
  let sLoop := (List.range p.loopCount).foldl
    (fun s idx => arun idx s p.body) sEntry
  let sFinal := arun 0 sLoop p.epilogue
  change aFinal.regs (auditReg p.regCount) = 0 →
    p.runFromArray arr = some sFinal ∧
      SourceAgree p.regCount aFinal sFinal
  intro hfinalZero
  have hzeroWord := initialAStateWithArray_word arr harr
  have hzeroAudit :
      (initialAStateWithArray arr).regs (auditReg p.regCount) = 0 := by
    simp [initialAStateWithArray, initialState]
  have haEntryWord : WordState aEntry :=
    arun_word 0 (auditBlock p.arrayLen p.regCount p.init)
      (initialAStateWithArray arr) hzeroWord.1 hzeroWord.2
  have haLoopWord : WordState aLoop :=
    auditFold_word p.arrayLen p.regCount p.body
      (List.range p.loopCount) aEntry haEntryWord
  have hloopLe := auditBlock_audit_mono p.arrayLen p.regCount 0
    p.epilogue aLoop hp.2.2.2 haLoopWord hlen hlenM
  have hfinalZero' :
      (arun 0 aLoop (auditBlock p.arrayLen p.regCount p.epilogue)).regs
        (auditReg p.regCount) = 0 := by
    simpa only [aFinal] using hfinalZero
  have hloopZero : aLoop.regs (auditReg p.regCount) = 0 := by omega
  have hentryLe := auditFold_audit_mono p.arrayLen p.regCount p.body
    hp.2.2.1 hlen hlenM (List.range p.loopCount) aEntry haEntryWord
  have hloopZero' :
      ((List.range p.loopCount).foldl (fun st k =>
        arun k st (auditBlock p.arrayLen p.regCount p.body)) aEntry).regs
          (auditReg p.regCount) = 0 := by
    simpa only [aLoop] using hloopZero
  have hentryZero : aEntry.regs (auditReg p.regCount) = 0 := by omega
  have hinit := auditBlock_zero_sound p.arrayLen p.regCount 0 p.init
    (initialAStateWithArray arr) (initialAStateWithArray arr) hp.2.1
    hzeroWord (SourceAgree.refl p.regCount (initialAStateWithArray arr))
    hlen hlenM hzeroAudit hentryZero
  have hfold := auditFold_zero_sound p.arrayLen p.regCount p.body
    hp.2.2.1 hlen hlenM (List.range p.loopCount) aEntry sEntry
    haEntryWord hinit.2 hentryZero hloopZero
  have hepi := auditBlock_zero_sound p.arrayLen p.regCount 0 p.epilogue
    aLoop sLoop hp.2.2.2 haLoopWord hfold.2 hlen hlenM
    hloopZero hfinalZero
  have hinitDenote :
      denoteAInstrs p.arrayLen 0 (initialAStateWithArray arr) p.init =
        some sEntry :=
    denoteAInstrs_eq_arun p.arrayLen 0 p.init
      (initialAStateWithArray arr) hinit.1
  have hepiDenote :
      denoteAInstrs p.arrayLen 0 sLoop p.epilogue = some sFinal :=
    denoteAInstrs_eq_arun p.arrayLen 0 p.epilogue sLoop hepi.1
  constructor
  · simp [AProgram.runFromArray, hinitDenote, hfold.1, hepiDenote,
      sEntry, sLoop, sFinal]
  · exact hepi.2

/-- A rolled physical zero receipt for an audited consumer proves that the
original partial consumer has a source execution from the represented input
array. -/
theorem source_runFromArray_of_audit_rolled_zero
    (p : AProgram) (hp : p.WF) (base : Int) (hBase : BaseOk p.arrayLen base)
    (arr : Nat → Nat) (mem : Mem)
    (hCells : ∀ k, k < p.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (harr : ∀ k, arr k < M)
    (hlen : 0 < p.arrayLen) (hlenM : p.arrayLen < M)
    (hReceipt : Option.bind
      (evalMCCSequence
        ((auditProgram p).counterAugment.initialMCCWithMem base mem)
        (auditProgram p).rolledCompile)
      (fun m : MCCState => m.env ⟨(auditProgram p).output + 1⟩) =
        some (0 : Int)) :
    ∃ out, p.runFromArray arr = some out := by
  let aEntry := arun 0 (initialAStateWithArray arr)
    (auditBlock p.arrayLen p.regCount p.init)
  let aLoop := (List.range p.loopCount).foldl (fun s idx =>
    arun idx s (auditBlock p.arrayLen p.regCount p.body)) aEntry
  let aFinal := arun 0 aLoop
    (auditBlock p.arrayLen p.regCount p.epilogue)
  have hAuditRun : (auditProgram p).runFromArray arr = some aFinal := by
    simpa only [aEntry, aLoop, aFinal] using
      auditProgram_runFromArray p hp arr harr hlen hlenM
  have hAuditBase : BaseOk (auditProgram p).arrayLen base := by
    simpa [auditProgram] using hBase
  have hAuditCells : ∀ k, k < (auditProgram p).arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)) := by
    simpa [auditProgram] using hCells
  have hAuditCellsLt : ∀ k, k < (auditProgram p).arrayLen → arr k < M :=
    fun k _ => harr k
  have hzero : aFinal.regs (auditReg p.regCount) = 0 := by
    exact AProgram.output_eq_of_rolledCompile_fromArray
      (auditProgram p) (auditProgram_wf p hp) base hAuditBase arr mem
      hAuditCells hAuditCellsLt aFinal hAuditRun 0 hReceipt
  have hsound := auditProgram_zero_sound_fromArray p hp arr harr hlen hlenM
    hzero
  exact ⟨_, hsound.1⟩

#print axioms auditProgram_runFromArray
#print axioms auditProgram_zero_sound_fromArray
#print axioms source_runFromArray_of_audit_rolled_zero
#print axioms AProgram.runFromArray_word

end LeanCompCert.Verified.ArrayAudit

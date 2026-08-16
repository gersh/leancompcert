import LeanCompCert.Ports.R2ProductAudit
import LeanCompCert.Verified.ArrayAuditFromArray

/-!
# Source soundness of the combined R₂ product audit

The product guard is inserted before the generic fail-safe array audit.  This
file proves that the final one-word OR verdict recovers both (1) a defined run
of the product-instrumented source and (2) a zero product-overflow latch.
No production loop is evaluated by Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve.R2ProductAudit

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayAudit

private theorem or_lt_M {a b : Nat} (ha : a < M) (hb : b < M) :
    a ||| b < M := by
  simpa only [M] using Nat.or_lt_two_pow (by simpa only [M] using ha)
    (by simpa only [M] using hb)

private theorem or_eq_zero {a b : Nat} (h : a ||| b = 0) :
    a = 0 ∧ b = 0 := by
  have ha : a ≤ a ||| b := Nat.left_le_or
  have hb : b ≤ a ||| b := Nat.right_le_or
  omega

theorem combineAuditBody_run (s : AState) (hs : WordState s) :
    let out := arun 0 s combineAuditBody
    out.regs auditReg =
      (s.regs auditReg ||| s.regs runtimePartialAuditProgram.output) % M ∧
    out.arr = s.arr := by
  simp [combineAuditBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, AState.writeReg,
    denoteOperand, denoteOp, auditReg]

theorem combineAuditBody_zero_sound (s : AState) (hs : WordState s)
    (hzero : (arun 0 s combineAuditBody).regs auditReg = 0) :
    s.regs auditReg = 0 ∧
      s.regs runtimePartialAuditProgram.output = 0 := by
  have hrun := (combineAuditBody_run s hs).1
  have horLt := or_lt_M (hs.1 auditReg)
    (hs.1 runtimePartialAuditProgram.output)
  rw [Nat.mod_eq_of_lt horLt] at hrun
  exact or_eq_zero (hrun.symm.trans hzero)

/-- Exact total state of the generic partial-operation audit. -/
def partialEntry (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr) runtimePartialAuditProgram.init

def partialLoop (arr : Nat → Nat) : AState :=
  (List.range runtimePartialAuditProgram.loopCount).foldl
    (fun s idx => arun idx s runtimePartialAuditProgram.body)
    (partialEntry arr)

def partialFinal (arr : Nat → Nat) : AState :=
  arun 0 (partialLoop arr) runtimePartialAuditProgram.epilogue

def combinedFinal (arr : Nat → Nat) : AState :=
  arun 0 (partialFinal arr) combineAuditBody

theorem runtimePartialAudit_runFromArray (arr : Nat → Nat)
    (harr : ∀ j, arr j < M) :
    runtimePartialAuditProgram.runFromArray arr = some (partialFinal arr) := by
  simpa only [runtimePartialAuditProgram, partialEntry, partialLoop,
    partialFinal, LeanCompCert.Verified.ArrayAudit.auditProgram] using
    LeanCompCert.Verified.ArrayAudit.auditProgram_runFromArray
      runtimeProductSourceProgram runtimeProductSourceProgram_wf arr harr
      (by decide) (by decide)

/-- Appending the one total OR instruction changes only the epilogue and
output observation of the generic audit. -/
theorem runtimeProductAudit_runFromArray (arr : Nat → Nat)
    (harr : ∀ j, arr j < M) :
    runtimeProductAuditProgram.runFromArray arr = some (combinedFinal arr) := by
  let entry := partialEntry arr
  let step := fun idx s => arun idx s runtimePartialAuditProgram.body
  let fin := fun s => arun 0
    (arun 0 s runtimePartialAuditProgram.epilogue) combineAuditBody
  have hzero := initialAStateWithArray_word arr harr
  have hp := runtimeProductSourceProgram_wf
  have hInit : denoteAInstrs runtimeProductAuditProgram.arrayLen 0
      (initialAStateWithArray arr) runtimeProductAuditProgram.init =
        some entry := by
    simpa only [runtimeProductAuditProgram, runtimePartialAuditProgram,
      LeanCompCert.Verified.ArrayAudit.auditProgram, entry, partialEntry] using
      auditBlock_denote_arun runtimeProductSourceProgram.arrayLen
        runtimeProductSourceProgram.regCount 0 runtimeProductSourceProgram.init
        (initialAStateWithArray arr) hp.2.1 (by decide) (by decide)
        hzero.1 hzero.2
  have hEntryWord : WordState entry := by
    change WordState
      (arun 0 (initialAStateWithArray arr) runtimePartialAuditProgram.init)
    exact arun_word 0 runtimePartialAuditProgram.init
      (initialAStateWithArray arr) hzero.1 hzero.2
  have hStep : ∀ idx s, idx < runtimeProductAuditProgram.loopCount →
      WordState s →
      denoteAInstrs runtimeProductAuditProgram.arrayLen idx s
        runtimeProductAuditProgram.body = some (step idx s) := by
    intro idx s _ hs
    simpa only [runtimeProductAuditProgram, runtimePartialAuditProgram,
      LeanCompCert.Verified.ArrayAudit.auditProgram, step] using
      auditBlock_denote_arun runtimeProductSourceProgram.arrayLen
        runtimeProductSourceProgram.regCount idx runtimeProductSourceProgram.body
        s hp.2.2.1 (by decide) (by decide) hs.1 hs.2
  have hClosed : ∀ idx s, idx < runtimeProductAuditProgram.loopCount →
      WordState s → WordState (step idx s) := by
    intro idx s _ hs
    exact arun_word idx runtimePartialAuditProgram.body s hs.1 hs.2
  have hEpi : ∀ s, WordState s →
      denoteAInstrs runtimeProductAuditProgram.arrayLen 0 s
        runtimeProductAuditProgram.epilogue = some (fin s) := by
    intro s hs
    have hfirst := auditBlock_denote_arun
      runtimeProductSourceProgram.arrayLen runtimeProductSourceProgram.regCount
      0 runtimeProductSourceProgram.epilogue s hp.2.2.2
      (by decide) (by decide) hs.1 hs.2
    have hmidWord := arun_word 0 runtimePartialAuditProgram.epilogue s
      hs.1 hs.2
    have hlast : denoteAInstrs runtimeProductAuditProgram.arrayLen 0
        (arun 0 s runtimePartialAuditProgram.epilogue) combineAuditBody =
          some (arun 0 (arun 0 s runtimePartialAuditProgram.epilogue)
            combineAuditBody) := by
      apply denoteAInstrs_eq_arun
      simp [combineAuditBody, AllDefined, ADefined, denoteOp]
    rw [runtimeProductAuditProgram, denoteAInstrs_append]
    rw [show denoteAInstrs runtimePartialAuditProgram.arrayLen 0 s
        runtimePartialAuditProgram.epilogue =
          some (arun 0 s runtimePartialAuditProgram.epilogue) by
      simpa only [runtimePartialAuditProgram,
        LeanCompCert.Verified.ArrayAudit.auditProgram] using hfirst]
    exact hlast
  have hrun :=
    AProgram.runFromArray_eq_foldl_mem runtimeProductAuditProgram WordState
      step fin arr entry hInit hEntryWord hStep hClosed hEpi
  change runtimeProductAuditProgram.runFromArray arr =
    some (combinedFinal arr)
  change runtimeProductAuditProgram.runFromArray arr =
    some (arun 0
      (arun 0
        ((List.range runtimeProductAuditProgram.loopCount).foldl
          (fun s idx => arun idx s runtimePartialAuditProgram.body)
          (partialEntry arr))
        runtimePartialAuditProgram.epilogue)
      combineAuditBody)
  exact hrun

/-- Receipt-oriented packaging keeps a concrete caller from elaborating the
source program's enormous symbolic final-state expression. -/
private theorem auditProgram_run_zero_sound_exists_fromArray
    (p : AProgram) (hp : p.WF)
    (arr : Nat → Nat) (harr : ∀ j, arr j < M)
    (hlen : 0 < p.arrayLen) (hlenM : p.arrayLen < M)
    (auditedOut : AState)
    (hrunAudit : (LeanCompCert.Verified.ArrayAudit.auditProgram p).runFromArray
      arr = some auditedOut)
    (hzero : auditedOut.regs
      (LeanCompCert.Verified.ArrayAudit.auditReg p.regCount) = 0) :
    ∃ out, p.runFromArray arr = some out ∧
      SourceAgree p.regCount auditedOut out := by
  have hcanonical := auditProgram_runFromArray p hp arr harr hlen hlenM
  have hout : auditedOut =
      arun 0
        ((List.range p.loopCount).foldl
          (fun s idx => arun idx s
            (LeanCompCert.Verified.ArrayAudit.auditBlock
              p.arrayLen p.regCount p.body))
          (arun 0 (initialAStateWithArray arr)
            (LeanCompCert.Verified.ArrayAudit.auditBlock
              p.arrayLen p.regCount p.init)))
        (LeanCompCert.Verified.ArrayAudit.auditBlock
          p.arrayLen p.regCount p.epilogue) := by
    rw [hrunAudit] at hcanonical
    exact Option.some.inj hcanonical
  subst auditedOut
  have hsound := auditProgram_zero_sound_fromArray p hp arr harr
    hlen hlenM hzero
  exact ⟨_, hsound.1, hsound.2⟩

/-- A zero combined source verdict yields the product-instrumented source run
and its zero overflow latch.  Generic audit soundness supplies all partial
definedness; this theorem adds no receipt axiom. -/
theorem runtimeProductAudit_zero_sound_fromArray (arr : Nat → Nat)
    (harr : ∀ j, arr j < M)
    (hzero : (combinedFinal arr).regs auditReg = 0) :
    ∃ out,
      runtimeProductSourceProgram.runFromArray arr = some out ∧
      out.regs auditReg = 0 := by
  have hpartialWord : WordState (partialFinal arr) := by
    exact AProgram.runFromArray_word runtimePartialAuditProgram arr harr
      (partialFinal arr) (runtimePartialAudit_runFromArray arr harr)
  have hzeros := combineAuditBody_zero_sound (partialFinal arr) hpartialWord
    (by simpa only [combinedFinal] using hzero)
  have hlen : 0 < runtimeProductSourceProgram.arrayLen := by
    change 0 < runtimeProductionCfg.arrayLen
    decide
  have hlenM : runtimeProductSourceProgram.arrayLen < M := by
    change runtimeProductionCfg.arrayLen < M
    decide
  have hrunAudit := runtimePartialAudit_runFromArray arr harr
  change (LeanCompCert.Verified.ArrayAudit.auditProgram
    runtimeProductSourceProgram).runFromArray arr =
      some (partialFinal arr) at hrunAudit
  have hpartialZero406 := hzeros.2
  rw [runtimePartialAuditProgram_output] at hpartialZero406
  have hpartialZero : (partialFinal arr).regs
      (LeanCompCert.Verified.ArrayAudit.auditReg
        runtimeProductSourceProgram.regCount) = 0 := by
    rw [runtimeProductSourceProgram_genericAuditReg]
    exact hpartialZero406
  have hsound := auditProgram_run_zero_sound_exists_fromArray
    runtimeProductSourceProgram runtimeProductSourceProgram_wf arr harr
    hlen hlenM (partialFinal arr)
    hrunAudit hpartialZero
  rcases hsound with ⟨out, hrun, hagree⟩
  refine ⟨out, hrun, ?_⟩
  have hauditVisible : auditReg < runtimeProductSourceProgram.regCount := by
    rw [runtimeProductSourceProgram_regCount]
    decide
  exact (hagree.2 auditReg hauditVisible).symm.trans hzeros.1

#print axioms combineAuditBody_zero_sound
#print axioms runtimeProductAudit_runFromArray
#print axioms runtimeProductAudit_zero_sound_fromArray

end LeanCompCert.Ports.R2SegSieve.R2ProductAudit

import LeanCompCert.Verified.ArrayBridge
import LeanCompCert.Verified.ArrayFoldBridge

/-!
# Compiled source-rank scheduler for Proposition 12.2.4

The paper's finite range is the disjoint concatenation of two simple compiled
campaigns:

* `q = 1, ..., 3_299_999_999`;
* `q = 3_300_000_060 + 210 i` for `0 <= i < 89_047_619`.

Keeping these as two producers avoids both a dense sweep to `22*10^9` and a
branch inside every expensive per-`q` row. The small symbolic theorems below
identify the emitted register blocks with the exact source-rank map; no
production range is reduced by Lean.
-/

namespace LeanCompCert.Ports.Prop1224RankScheduler

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge

def denseRankEnd : Nat := 3_299_999_999
def firstExtensionQ : Nat := 3_300_000_060
def extensionDivisor : Nat := 210
def extensionRankCount : Nat := 89_047_619
def sourceRankCount : Nat := 3_389_047_618

/-- Exact paper-domain value assigned to a nonterminal source rank. -/
def qAtRank (rank : Nat) : Nat :=
  if rank < denseRankEnd then rank + 1
  else firstExtensionQ + (rank - denseRankEnd) * extensionDivisor

def rQ : Nat := 0
def rScaled : Nat := 1
def rCount : Nat := 2
def rChecksum : Nat := 3
def regCount : Nat := 4

/-- Dense campaign: the loop index is one below `q`. -/
def denseBody : List AInstr :=
  [ .scalar (.binop rQ .add .idx (.lit 1)) ]

/-- Sparse campaign: its local loop index starts at the first new multiple of
`210`, immediately after the dense range. -/
def extensionBody : List AInstr :=
  [ .scalar (.binop rScaled .mul .idx (.lit extensionDivisor))
  , .scalar (.binop rQ .add (.lit firstExtensionQ) (.reg rScaled)) ]

def withBenchmarkCounters (body : List AInstr) : List AInstr := body ++
  [ .scalar (.binop rCount .add (.reg rCount) (.lit 1))
  , .scalar (.binop rChecksum .add (.reg rChecksum) (.reg rQ)) ]

def denseProgram : AProgram := {
  regCount := regCount
  arrayLen := 1
  loopCount := denseRankEnd
  init := []
  body := withBenchmarkCounters denseBody
  epilogue := []
  output := rChecksum
}

def extensionProgram : AProgram := {
  regCount := regCount
  arrayLen := 1
  loopCount := extensionRankCount
  init := []
  body := withBenchmarkCounters extensionBody
  epilogue := []
  output := rChecksum
}

theorem denseProgram_wf : denseProgram.WF := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simp [denseProgram]
  · intro i hi
    simp only [denseProgram, withBenchmarkCounters, denseBody,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide
  · simp [denseProgram]

theorem extensionProgram_wf : extensionProgram.WF := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simp [extensionProgram]
  · intro i hi
    simp only [extensionProgram, withBenchmarkCounters, extensionBody,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with (rfl | rfl) | rfl | rfl <;> decide
  · simp [extensionProgram]

theorem denseProgram_compiled (base : Int)
    (hBase : BaseOk denseProgram.arrayLen base)
    (n : Nat) (hDenote : denseProgram.denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          (denseProgram.initialMCC base) denseProgram.compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨denseProgram.output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ denseProgram_wf base hBase n hDenote

theorem extensionProgram_compiled (base : Int)
    (hBase : BaseOk extensionProgram.arrayLen base)
    (n : Nat) (hDenote : extensionProgram.denote = some n) :
    Option.bind
        (Verified.MemFragment.evalMCCSequence
          (extensionProgram.initialMCC base) extensionProgram.compile)
        (fun m : Verified.MemFragment.MCCState =>
          m.env ⟨extensionProgram.output + 1⟩) = some ((n : Nat) : Int) :=
  AProgram.evalCC_compile _ extensionProgram_wf base hBase n hDenote

/-- The dense compiled block computes its exact `q`. -/
theorem denseBody_q (rank : Nat) (s : AState)
    (hrank : rank < denseRankEnd) :
    (arun rank s denseBody).regs rQ = rank + 1 := by
  have hfit : rank + 1 < M := by
    unfold denseRankEnd M at *
    omega
  simp [denseBody, arun, astep, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rQ, Nat.mod_eq_of_lt hfit]

/-- The sparse compiled block computes its exact multiple-of-210 `q`. -/
theorem extensionBody_q (localRank : Nat) (s : AState)
    (hrank : localRank < extensionRankCount) :
    (arun localRank s extensionBody).regs rQ =
      firstExtensionQ + localRank * extensionDivisor := by
  have hrankM : localRank < M := by
    unfold extensionRankCount M at *
    omega
  have hscaled : localRank * extensionDivisor < M := by
    unfold extensionRankCount extensionDivisor M at *
    omega
  have hq : firstExtensionQ + localRank * extensionDivisor < M := by
    unfold extensionRankCount extensionDivisor firstExtensionQ M at *
    omega
  simp [extensionBody, arun, astep,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    AState.writeReg, rQ, rScaled, Nat.mod_eq_of_lt hrankM,
    Nat.mod_eq_of_lt hscaled, Nat.mod_eq_of_lt hq]

theorem sourceRankCount_eq :
    sourceRankCount = denseRankEnd + extensionRankCount := by decide

theorem qAtRank_dense {rank : Nat} (h : rank < denseRankEnd) :
    qAtRank rank = rank + 1 := by simp [qAtRank, h]

theorem qAtRank_extension {localRank : Nat}
    (h : localRank < extensionRankCount) :
    qAtRank (denseRankEnd + localRank) =
      firstExtensionQ + localRank * extensionDivisor := by
  have hn : ¬denseRankEnd + localRank < denseRankEnd := by omega
  simp [qAtRank, hn]

theorem qAtRank_zero : qAtRank 0 = 1 := by decide

theorem qAtRank_last :
    qAtRank (sourceRankCount - 1) = 21_999_999_840 := by decide

#print axioms denseBody_q
#print axioms extensionBody_q
#print axioms denseProgram_compiled
#print axioms extensionProgram_compiled

end LeanCompCert.Ports.Prop1224RankScheduler

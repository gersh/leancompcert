import LeanCompCert.Ports.Prop1224CellGuardedSemantics
import LeanCompCert.Ports.Prop1224CellMarkBudget
import LeanCompCert.Ports.Prop1224CellAccInactiveSemantics

/-!
# Causal projection of the Proposition 12.2.4 marking-budget signal

The guarded signed artifact latches register `80` after every literal body.
This module identifies that register with the exact source-level budget
predicate at the input of the final five-instruction marking guard.  The
result lets source denotation proofs obtain the two addition no-wrap premises
from acceptance and `WordState`, without evaluating the marking schedule or
assuming room in either accumulated failure counter.
-/

namespace LeanCompCert.Ports.Prop1224Cell

set_option maxRecDepth 100000

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.Prop1224CellGuarded
open LeanCompCert.Ports.Prop1224CellGuardedSemantics

/-- Literal prefix immediately before the five marking-budget instructions. -/
def p1224MarkBeforeBudgetBody (c : CellCfg) : List AInstr :=
  c.markBody.take 81

theorem markBody_eq_beforeBudget_append (c : CellCfg) :
    c.markBody = p1224MarkBeforeBudgetBody c ++ p1224MarkBudgetBody c := by
  rfl

/-- Register `80` at the end of the complete source body is exactly the
source budget-failure predicate computed at the budget block boundary.  The
post-marking phases frame this local signal. -/
theorem body_markBudgetSignal_eq (c : CellCfg) (k : Nat) (s : AState)
    (hT : c.markSteps < M) (hK : c.tableLen < M) :
    let beforeBudget := arun k s (p1224MarkBeforeBudgetBody c)
    (arun k s c.body).regs 80 =
      c.p1224BudgetFailure (beforeBudget.regs rR) (beforeBudget.regs rPi) := by
  let beforeBudget := arun k s (p1224MarkBeforeBudgetBody c)
  let marked := arun k beforeBudget (p1224MarkBudgetBody c)
  let accumulated := arun k marked c.accBody
  let logged := arun k accumulated c.logBody
  have hsignal := p1224MarkBudgetBody_signal_run c k beforeBudget hT hK
  have hacc : accumulated.regs 80 = marked.regs 80 :=
    accBody_reg_frame c 80 k marked (by rfl)
      (by decide) (by decide) (by decide) (by rfl) (by rfl) (by rfl)
  have hlog : logged.regs 80 = accumulated.regs 80 :=
    arun_frame k 80 c.logBody (by rfl) accumulated
  have htail : (arun k logged c.tailBody).regs 80 = logged.regs 80 :=
    arun_frame k 80 c.tailBody (by rfl) logged
  rw [CellCfg.body, markBody_eq_beforeBudget_append]
  simp only [arun_append]
  exact htail.trans (hlog.trans (hacc.trans hsignal))

/-- Acceptance turns the exact local signal into a zero source budget
predicate at any symbolic source prefix. -/
theorem guardedProgram_denote_zero_projected_markBudgetFailure
    (c : CellCfg) (seed : CellSeed)
    (hDenote :
      (guardedProgram c seed).denote = some 0)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (j : Nat) (hj : j < c.period * c.segCount) :
    let entry := arun 0 initialAState (c.init seed)
    let sourceBefore := (List.range j).foldl
      (fun st idx => arun idx st c.body) entry
    let beforeBudget :=
      arun j sourceBefore (p1224MarkBeforeBudgetBody c)
    c.p1224BudgetFailure (beforeBudget.regs rR)
      (beforeBudget.regs rPi) = 0 := by
  let entry := arun 0 initialAState (c.init seed)
  let sourceBefore := (List.range j).foldl
    (fun st idx => arun idx st c.body) entry
  let beforeBudget :=
    arun j sourceBefore (p1224MarkBeforeBudgetBody c)
  have hzero := guardedProgram_denote_zero_projected_mark_signal
    c seed hDenote j hj
  change (arun j sourceBefore c.body).regs 80 = 0 at hzero
  have hsignal := body_markBudgetSignal_eq c j sourceBefore hT hK
  change (arun j sourceBefore c.body).regs 80 =
    c.p1224BudgetFailure (beforeBudget.regs rR)
      (beforeBudget.regs rPi) at hsignal
  rw [hsignal] at hzero
  exact hzero

/-- The accepted zero signal supplies both budget-addition word guards at the
literal block boundary.  Only the universal machine word invariant is used;
neither counter has to be precomputed or assumed to be zero. -/
theorem guardedProgram_denote_zero_projected_markBudgetWordGuards
    (c : CellCfg) (seed : CellSeed)
    (hDenote :
      (guardedProgram c seed).denote = some 0)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (j : Nat) (hj : j < c.period * c.segCount) :
    let entry := arun 0 initialAState (c.init seed)
    let sourceBefore := (List.range j).foldl
      (fun st idx => arun idx st c.body) entry
    let beforeBudget :=
      arun j sourceBefore (p1224MarkBeforeBudgetBody c)
    beforeBudget.regs rViol +
          c.p1224BudgetFailure (beforeBudget.regs rR)
            (beforeBudget.regs rPi) < M ∧
      beforeBudget.regs rVMark +
          c.p1224BudgetFailure (beforeBudget.regs rR)
            (beforeBudget.regs rPi) < M := by
  let entry := arun 0 initialAState (c.init seed)
  let sourceBefore := (List.range j).foldl
    (fun st idx => arun idx st c.body) entry
  let beforeBudget :=
    arun j sourceBefore (p1224MarkBeforeBudgetBody c)
  have hentryWord : WordState entry :=
    arun_word 0 (c.init seed) initialAState
      initialAState_word.1 initialAState_word.2
  have hbeforeWord : WordState sourceBefore :=
    foldl_arun_word c.body (List.range j) entry
      hentryWord.1 hentryWord.2
  have hbudgetWord : WordState beforeBudget :=
    arun_word j (p1224MarkBeforeBudgetBody c) sourceBefore
      hbeforeWord.1 hbeforeWord.2
  have hfailure :=
    guardedProgram_denote_zero_projected_markBudgetFailure
      c seed hDenote hT hK j hj
  change c.p1224BudgetFailure (beforeBudget.regs rR)
    (beforeBudget.regs rPi) = 0 at hfailure
  dsimp only
  rw [hfailure]
  simpa only [Nat.add_zero] using
    And.intro (hbudgetWord.1 rViol) (hbudgetWord.1 rVMark)

#print axioms markBody_eq_beforeBudget_append
#print axioms body_markBudgetSignal_eq
#print axioms guardedProgram_denote_zero_projected_markBudgetFailure
#print axioms guardedProgram_denote_zero_projected_markBudgetWordGuards

end LeanCompCert.Ports.Prop1224Cell

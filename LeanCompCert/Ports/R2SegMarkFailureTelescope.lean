import LeanCompCert.Ports.R2RuntimeFailureObservation
import LeanCompCert.Ports.R2RuntimeWindowPosition
import LeanCompCert.Ports.R2SegMarkingBudget
import LeanCompCert.Ports.R2SegWindowPosition

/-!
# Telescope for the compiled R2 marking-budget failure counter

The production body has exactly one writer of `rVMark`: the final five
instructions of `markBody`.  This file isolates that writer and proves a
size-independent fold bound.  Consequently a retained terminal zero rules
out a failed marking-budget check at every production iteration, without
evaluating the production fold in Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve

set_option maxRecDepth 20000

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame

/-- The literal marking block before its five-instruction budget guard. -/
def markBeforeBudgetBody (c : R2Cfg) : List AInstr := c.markBody.take 96

theorem markBody_eq_before_budget (c : R2Cfg) :
    c.markBody = markBeforeBudgetBody c ++ markBudgetBody c := by
  rfl

/-- Projection of the budget guard needed for the counter telescope.  The
shared `rViol` addition may wrap in the total model; the independently stored
`rVMark` addition is exact under the one explicit room premise below. -/
theorem markBudgetBody_vmark_run (c : R2Cfg) (k : Nat) (s : AState)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hroom : s.regs rVMark +
      c.budgetFailure (s.regs rR) (s.regs rPi) < M) :
    (arun k s (markBudgetBody c)).regs rVMark =
      s.regs rVMark + c.budgetFailure (s.regs rR) (s.regs rPi) := by
  have hTm1 : c.markSteps - 1 < M :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hT
  have hKMod : c.tableLen % M = c.tableLen := Nat.mod_eq_of_lt hK
  have hTm1Mod : (c.markSteps - 1) % M = c.markSteps - 1 :=
    Nat.mod_eq_of_lt hTm1
  have honeMod : (1 : Nat) % M = 1 := Nat.mod_eq_of_lt (by decide)
  by_cases hr : s.regs rR = c.markSteps - 1
  · by_cases hp : s.regs rPi = c.tableLen
    · have hr5 : s.regs 5 = c.markSteps - 1 := by simpa [rR] using hr
      have hp2 : s.regs 2 = c.tableLen := by simpa [rPi] using hp
      have hm : s.regs rVMark < M := by
        simpa [R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp] using hroom
      have hm353 : s.regs 353 < M := by simpa [rVMark] using hm
      simp [markBudgetBody, markBudgetInstrs, arun, astep, AState.writeReg,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp, hr5, hp2,
        rR, rPi, rViol, rVMark,
        hTm1Mod, hKMod, Nat.mod_eq_of_lt hm353]
    · have hr5 : s.regs 5 = c.markSteps - 1 := by simpa [rR] using hr
      have hp2 : s.regs 2 ≠ c.tableLen := by simpa [rPi] using hp
      have hm : s.regs rVMark + 1 < M := by
        simpa [R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp] using hroom
      have hm353 : s.regs 353 + 1 < M := by simpa [rVMark] using hm
      simp [markBudgetBody, markBudgetInstrs, arun, astep, AState.writeReg,
        LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hp, hr5, hp2,
        rR, rPi, rViol, rVMark,
        hTm1Mod, hKMod, honeMod, Nat.mod_eq_of_lt hm353]
  · have hr5 : s.regs 5 ≠ c.markSteps - 1 := by simpa [rR] using hr
    have hm : s.regs rVMark < M := by
      simpa [R2Cfg.budgetFailure, eqBitR2, neBitR2, hr] using hroom
    have hm353 : s.regs 353 < M := by simpa [rVMark] using hm
    simp [markBudgetBody, markBudgetInstrs, arun, astep, AState.writeReg,
      LeanCompCert.Verified.InstrBlock.sdest,
      LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
      R2Cfg.budgetFailure, eqBitR2, neBitR2, hr, hr5,
      rR, rPi, rViol, rVMark,
      hTm1Mod, hKMod, Nat.mod_eq_of_lt hm353]

/-- One complete scheduled body adds exactly the Boolean budget-failure bit
computed after the marking transition.  All later phases frame `rVMark`. -/
theorem body_vmark_increment (c : R2Cfg) (k : Nat) (s : AState)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hroom :
      let marked := arun k s (markBeforeBudgetBody c)
      s.regs rVMark + c.budgetFailure (marked.regs rR) (marked.regs rPi) < M) :
    let marked := arun k s (markBeforeBudgetBody c)
    (arun k s c.body).regs rVMark =
      s.regs rVMark + c.budgetFailure (marked.regs rR) (marked.regs rPi) := by
  let marked := arun k s (markBeforeBudgetBody c)
  have hmarkFrame : marked.regs rVMark = s.regs rVMark :=
    arun_frame k rVMark (markBeforeBudgetBody c) (by rfl) s
  let guarded := arun k marked (markBudgetBody c)
  have hguard := markBudgetBody_vmark_run c k marked hT hK (by
    rw [hmarkFrame]
    exact hroom)
  have hsuffix :
      (arun k guarded (c.classBody ++ c.logBody ++ c.tailBody)).regs rVMark =
        guarded.regs rVMark :=
    arun_frame k rVMark (c.classBody ++ c.logBody ++ c.tailBody)
      (by rfl) guarded
  rw [body_eq_mark_post, markPostBody, markBody_eq_before_budget,
    arun_append, arun_append, arun_append, arun_append]
  rw [hmarkFrame] at hguard
  exact hsuffix.trans hguard

theorem budgetFailure_le_one (c : R2Cfg) (r pi : Nat) :
    c.budgetFailure r pi ≤ 1 := by
  simp only [R2Cfg.budgetFailure, eqBitR2, neBitR2]
  split <;> split <;> omega

/-- Across an arbitrary list of scheduled bodies, `rVMark` can only grow,
and it grows by at most one per iteration. -/
theorem foldl_body_vmark_bounds (c : R2Cfg) (indices : List Nat) (s : AState)
    (hT : c.markSteps < M) (hK : c.tableLen < M)
    (hroom : s.regs rVMark + indices.length < M) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    s.regs rVMark ≤ out.regs rVMark ∧
      out.regs rVMark ≤ s.regs rVMark + indices.length := by
  induction indices generalizing s with
  | nil => simp
  | cons k ks ih =>
      let marked := arun k s (markBeforeBudgetBody c)
      let bit := c.budgetFailure (marked.regs rR) (marked.regs rPi)
      have hbit : bit ≤ 1 := budgetFailure_le_one c _ _
      have hfirstRoom : s.regs rVMark + bit < M := by
        simp only [List.length_cons] at hroom
        omega
      have hfirst := body_vmark_increment c k s hT hK hfirstRoom
      change (arun k s c.body).regs rVMark = s.regs rVMark + bit at hfirst
      have htailRoom :
          (arun k s c.body).regs rVMark + ks.length < M := by
        rw [hfirst]
        simp only [List.length_cons] at hroom
        omega
      have htail := ih (s := arun k s c.body) htailRoom
      dsimp only at htail
      simp only [List.foldl]
      constructor
      · calc
          s.regs rVMark ≤ s.regs rVMark + bit := Nat.le_add_right _ _
          _ = (arun k s c.body).regs rVMark := hfirst.symm
          _ ≤ _ := htail.1
      · calc
          (ks.foldl (fun st k => arun k st c.body)
              (arun k s c.body)).regs rVMark
              ≤ (arun k s c.body).regs rVMark + ks.length := htail.2
          _ = s.regs rVMark + bit + ks.length := by rw [hfirst]
          _ ≤ s.regs rVMark + (ks.length + 1) := by omega

theorem runtimeProductionEntry_vmark_zero :
    runtimeProductionEntry.regs rVMark = 0 := by
  have hframe := arun_frame 0 rVMark
    (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).init
    (by rfl)
    (initialAStateWithArray runtimeProductionPacked.arr)
  rw [runtimeProductionEntry, hframe]
  rfl

theorem runtimeProductionLoopOut_eq_fold :
    runtimeProductionLoopOut =
      (List.range (runtimeProductionCfg.period *
        runtimeProductionCfg.segCount)).foldl
        (fun s index => arun index s runtimeProductionCfg.body)
        runtimeProductionEntry := by
  rfl

/-- Exact total-state prefix before loop index `j`. -/
def bodyPrefix (c : R2Cfg) (entry : AState) (j : Nat) : AState :=
  (List.range j).foldl
    (fun s index => arun index s c.body) entry

/-- State at the unique marking-budget guard within loop index `j`. -/
def beforeBudget (c : R2Cfg) (entry : AState) (j : Nat) : AState :=
  arun j (bodyPrefix c entry j) (markBeforeBudgetBody c)

def runtimeProductionPrefix (j : Nat) : AState :=
  bodyPrefix runtimeProductionCfg runtimeProductionEntry j

def runtimeProductionBeforeBudget (j : Nat) : AState :=
  beforeBudget runtimeProductionCfg runtimeProductionEntry j

/-- Every dynamic invocation of the literal marking-budget guard passed in
the retained production execution.  This is the per-round fact needed by the
window marking telescope; the long range is never evaluated in Lean. -/
theorem runtimeProduction_every_mark_budget_passes :
    ∀ j, j < runtimeProductionCfg.period * runtimeProductionCfg.segCount →
      runtimeProductionCfg.budgetFailure
        ((runtimeProductionBeforeBudget j).regs rR)
        ((runtimeProductionBeforeBudget j).regs rPi) = 0 := by
  intro j hj
  let c := runtimeProductionCfg
  let N := c.period * c.segCount
  let pre := runtimeProductionPrefix j
  let marked := runtimeProductionBeforeBudget j
  let bit := c.budgetFailure (marked.regs rR) (marked.regs rPi)
  let after := arun j pre c.body
  change j < N at hj
  have hentry : runtimeProductionEntry.regs rVMark = 0 :=
    runtimeProductionEntry_vmark_zero
  have hNM : N < M := by
    dsimp only [N, c]
    decide
  have hpreBounds := foldl_body_vmark_bounds c (List.range j)
    runtimeProductionEntry (by decide) (by decide) (by
      rw [hentry]
      simp only [List.length_range, Nat.zero_add]
      omega)
  have hpreLe : pre.regs rVMark ≤ j := by
    simpa only [pre, runtimeProductionPrefix, bodyPrefix, c, List.length_range,
      hentry, Nat.zero_add] using
      hpreBounds.2
  have hbitLe : bit ≤ 1 := budgetFailure_le_one c _ _
  have hfirstRoom : pre.regs rVMark + bit < M := by omega
  have hfirst := body_vmark_increment c j pre (by decide) (by decide)
    hfirstRoom
  change after.regs rVMark = pre.regs rVMark + bit at hfirst
  have hafterLe : after.regs rVMark ≤ j + 1 := by omega
  let tailLen := N - (j + 1)
  let tail := List.range' (j + 1) tailLen
  have hcount : N = (j + 1) + tailLen := by
    dsimp only [tailLen]
    omega
  have hrange : List.range N = List.range j ++ j :: tail := by
    rw [hcount, List.range_eq_range',
      ← List.range'_append_1 (s := 0) (m := j + 1) (n := tailLen),
      List.range'_1_concat, ← List.range_eq_range']
    simp only [Nat.zero_add, List.append_assoc, List.singleton_append, tail]
  have htailRoom : after.regs rVMark + tail.length < M := by
    have htailLength : tail.length = tailLen := by simp [tail]
    rw [htailLength]
    omega
  have htailBounds := foldl_body_vmark_bounds c tail after
    (by decide) (by decide) htailRoom
  dsimp only at htailBounds
  have hloopZero := runtimeProduction_verified_no_mark_or_drain_failure.1
  rw [runtimeProductionLoopOut_eq_fold] at hloopZero
  have hloopZero' :
    ((List.range N).foldl (fun s index => arun index s c.body)
      runtimeProductionEntry).regs rVMark = 0 := by
    simpa only [N, c] using hloopZero
  rw [hrange, List.foldl_append] at hloopZero'
  change
    (tail.foldl (fun s index => arun index s c.body) after).regs rVMark = 0
      at hloopZero'
  have hafterZero : after.regs rVMark = 0 := by
    omega
  change bit = 0
  omega

/-- A zero budget bit at every scheduled round forces table exhaustion at the
last marking round of every window.  This theorem is generic, so its proof
term never expands the concrete production configuration. -/
theorem every_window_table_exhausted_of_passes (c : R2Cfg) (entry : AState)
    (hentryR : entry.regs rR = 0) (hentryW : entry.regs rW = c.lo)
    (hperiod0 : 0 < c.period) (hperiodM : c.period < M)
    (hsegLen : 0 < c.segLen)
    (hspan : c.lo + c.segCount * c.segLen < M)
    (hlast : c.markSteps - 1 < c.period)
    (hpasses : ∀ j, j < c.period * c.segCount →
      c.budgetFailure ((beforeBudget c entry j).regs rR)
        ((beforeBudget c entry j).regs rPi) = 0) :
    ∀ q, q < c.segCount →
      (beforeBudget c entry
        (q * c.period + (c.markSteps - 1))).regs rPi = c.tableLen := by
  intro q hq
  let j := q * c.period + (c.markSteps - 1)
  let before := bodyWindowPrefix c entry q
  let pre := bodyPrefix c entry j
  let marked := beforeBudget c entry j
  have hqmul := Nat.mul_le_mul_right c.segLen (Nat.le_of_lt hq)
  have hbefore := bodyWindowPrefix_position c q entry c.lo hentryR hentryW
    hperiod0 hperiodM (by omega)
  change before.regs rR = 0 ∧
    before.regs rW = c.lo + q * c.segLen at hbefore
  have hpreEq : pre =
      (List.range' (q * c.period) (c.markSteps - 1)).foldl
        (fun s index => arun index s c.body) before := by
    dsimp only [pre, bodyPrefix, j, before]
    rw [show q * c.period = c.period * q by exact Nat.mul_comm _ _,
      List.range_add, List.foldl_append, ← List.range'_eq_map_range,
      ← bodyWindowPrefix_eq_range]
  let markIndices := List.range' (q * c.period) (c.markSteps - 1)
  have hmarkPos := foldl_body_mark_position c markIndices before 0
    (c.lo + q * c.segLen) hbefore.1 hbefore.2 (by
      simp [markIndices]) hsegLen hperiodM (by omega)
  have hpreR : pre.regs rR = c.markSteps - 1 := by
    rw [hpreEq]
    simpa only [markIndices, List.length_range', Nat.zero_add] using hmarkPos.1
  have hmarkedFrame : marked.regs rR = pre.regs rR := by
    have hf := arun_frame j rR (markBeforeBudgetBody c) (by rfl) pre
    simpa only [marked, beforeBudget, pre] using hf
  have hmarkedR : marked.regs rR = c.markSteps - 1 :=
    hmarkedFrame.trans hpreR
  have hj : j < c.period * c.segCount := by
    have hq1 : q + 1 ≤ c.segCount := by omega
    have hmul := Nat.mul_le_mul_right c.period hq1
    have hjNext : j < (q + 1) * c.period := by
      have hadd := Nat.add_lt_add_left hlast (q * c.period)
      simpa only [j, Nat.add_mul, Nat.one_mul] using hadd
    calc
      j < (q + 1) * c.period := hjNext
      _ ≤ c.segCount * c.period := hmul
      _ = c.period * c.segCount := Nat.mul_comm _ _
  have hpass := hpasses j hj
  change c.budgetFailure (marked.regs rR) (marked.regs rPi) = 0 at hpass
  rw [hmarkedR] at hpass
  have hneZero : neBitR2 (marked.regs rPi) c.tableLen = 0 := by
    simpa [R2Cfg.budgetFailure, eqBitR2] using hpass
  by_cases heq : marked.regs rPi = c.tableLen
  · exact heq
  · simp [neBitR2, heq] at hneZero

/-- At the last marking round of every production window, the post-marking
cursor is exactly the table sentinel.  Thus the compiled receipt certifies
that no prime-power row was omitted in any window. -/
theorem runtimeProduction_every_window_table_exhausted :
    ∀ q, q < runtimeProductionCfg.segCount →
      (runtimeProductionBeforeBudget
        (q * runtimeProductionCfg.period +
          (runtimeProductionCfg.markSteps - 1))).regs rPi =
        runtimeProductionCfg.tableLen := by
  have hentry := runtimeEntry_position runtimeProductionCfg
    runtimeProductionSeed runtimeProductionPacked.arr (by decide)
  change runtimeProductionEntry.regs rR = 0 ∧
    runtimeProductionEntry.regs rW = runtimeProductionCfg.lo at hentry
  simpa only [runtimeProductionBeforeBudget, beforeBudget] using
    every_window_table_exhausted_of_passes runtimeProductionCfg
      runtimeProductionEntry hentry.1 hentry.2 (by decide) (by decide)
      (by decide) (by decide) (by decide)
      runtimeProduction_every_mark_budget_passes

#print axioms body_vmark_increment
#print axioms foldl_body_vmark_bounds
#print axioms runtimeProduction_every_mark_budget_passes
#print axioms runtimeProduction_every_window_table_exhausted

end LeanCompCert.Ports.R2SegSieve

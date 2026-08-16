import LeanCompCert.Ports.R2SegDrainFailureTelescope

/-!
# Telescope for the compiled R2 stream-capacity failure counter

The classifier contains the only writer of `rVCap`.  As with the marking and
drain counters, the purpose of this file is to turn the terminal zero retained
from compiled execution into a statement about every dynamic capacity guard,
without replaying the production loop in Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve

set_option maxRecDepth 20000

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayScalarBlock

/-- Classifier prefix through the shared violation update, immediately before
the independent `rVCap` update. -/
def classBeforeVCapBody (c : R2Cfg) : List AInstr := c.classBody.take 51

/-- The unique instruction writing `rVCap`. -/
def classVCapCommitBody (c : R2Cfg) : List AInstr :=
  (c.classBody.drop 51).take 1

/-- Remaining classifier instructions after the capacity-counter write. -/
def classAfterVCapBody (c : R2Cfg) : List AInstr := c.classBody.drop 52

theorem classBody_eq_vcap_stages (c : R2Cfg) :
    c.classBody = classBeforeVCapBody c ++ classVCapCommitBody c ++
      classAfterVCapBody c := by
  rfl

/-- Prefix ending immediately before the scalar selector. -/
def classBeforeSelectorBody (c : R2Cfg) : List AInstr :=
  classBeforeClearBody c ++ classClearBody c

/-- First four compaction instructions, through the shared violation write. -/
def classCapPrepBody (c : R2Cfg) : List AInstr :=
  (classCompactPrefixBody c).take 4

theorem classBeforeVCapBody_eq_stages (c : R2Cfg) :
    classBeforeVCapBody c = classBeforeSelectorBody c ++
      classSelectBody c ++ classCapPrepBody c := by
  rfl

/-- The classifier's active bit is always Boolean.  The only arithmetic fact
needed is that the two phase thresholds have not wrapped. -/
theorem markBody_class_active_le_one (c : R2Cfg) (k : Nat) (s : AState)
    (hTL : c.markSteps + c.segLen < M) :
    (arun k s c.markBody).regs 9 ≤ 1 := by
  let phased := arun k s (markPhaseBody c)
  have hsuffix :
      (arun k phased (markAfterPhaseBody c)).regs 9 = phased.regs 9 :=
    arun_frame k 9 (markAfterPhaseBody c) (by rfl) phased
  rw [markBody_eq_phase_stages, arun_append, hsuffix]
  have hT : c.markSteps < M := by omega
  have h1 : (1 : Nat) < M := by decide
  simp [phased, markPhaseBody, markPhaseInstrs, arun, astep,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp, rR,
    Nat.mod_eq_of_lt hT, Nat.mod_eq_of_lt hTL, Nat.mod_eq_of_lt h1]
  split <;> split <;> simp [M] <;> omega

/-- The comparison which detects a remaining large factor is Boolean after
the literal classifier read prefix. -/
theorem classBeforeSelector_large_le_one (c : R2Cfg) (k : Nat) (s : AState) :
    (arun k s (classBeforeSelectorBody c)).regs 95 ≤ 1 := by
  let before := arun k s (classBeforeClearBody c)
  have hbefore : before.regs 95 ≤ 1 := by
    simp [before, classBeforeClearBody, R2Cfg.classBody, arun, astep,
      AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      rR, rW]
    split <;> split <;> simp [M]
  have hframe :
      (arun k before (classClearBody c)).regs 95 = before.regs 95 :=
    arun_frame k 95 (classClearBody c) (by rfl) before
  rw [classBeforeSelectorBody, arun_append, hframe]
  exact hbefore

/-- The selector's push word is Boolean whenever its large-factor and active
inputs are Boolean.  No bound on the decoded count is needed: counts other
than zero, one, or two simply select no mode. -/
theorem classFlagInstrs_push_le_one (k : Nat) (s : RegState)
    (hlarge : s 95 ≤ 1) (hactive : s 9 ≤ 1) :
    (srun k s classFlagInstrs) 116 ≤ 1 := by
  have hl : s 95 = 0 ∨ s 95 = 1 := by omega
  rcases hl with hl | hl <;>
    by_cases h0 : s 96 = 0 <;>
    by_cases h1 : s 96 = 1 <;>
    by_cases h2 : s 96 = 2 <;>
    simp_all [classFlagInstrs, srun, RegState.set, sdest, sval,
      denoteOperand, denoteOp, M, Nat.mod_eq_of_lt] <;> omega

theorem classSelectBody_push_le_one (c : R2Cfg) (k : Nat) (s : AState)
    (hlarge : s.regs 95 ≤ 1) (hactive : s.regs 9 ≤ 1) :
    (arun k s (classSelectBody c)).regs 116 ≤ 1 := by
  let flags := arun k s (lift classFlagInstrs)
  have hflags : flags.regs 116 ≤ 1 := by
    change (arun k s (lift classFlagInstrs)).regs 116 ≤ 1
    rw [arun_lift_regs]
    exact classFlagInstrs_push_le_one k s.regs hlarge hactive
  have hsuffix :
      (arun k flags (lift (classModeInstrs ++ classPayloadInstrs))).regs
          116 = flags.regs 116 :=
    arun_frame k 116 (lift (classModeInstrs ++ classPayloadInstrs))
      (by rfl) flags
  rw [classSelectBody_eq_selector, classSelectorBody, classSelectorInstrs,
    List.append_assoc, lift_append, arun_append]
  rw [hsuffix]
  exact hflags

/-- The capacity predicate `push - doPush` is Boolean. -/
theorem classCapPrep_bit_le_one (c : R2Cfg) (k : Nat) (s : AState)
    (hpush : s.regs 116 ≤ 1) :
    (arun k s (classCapPrepBody c)).regs 131 ≤ 1 := by
  have hp : s.regs 116 = 0 ∨ s.regs 116 = 1 := by omega
  rcases hp with hp | hp <;>
    simp [classCapPrepBody, classCompactPrefixBody, R2Cfg.classBody,
      arun, astep, AState.writeReg, sdest, sval, denoteOperand, denoteOp,
      hp, rWc, rViol, M] <;>
    split <;> simp [M]

/-- The literal capacity-failure value is Boolean for every state in which
the classifier active bit is Boolean. -/
theorem classBeforeVCap_bit_le_one (c : R2Cfg) (k : Nat) (s : AState)
    (hactive : s.regs 9 ≤ 1) :
    (arun k s (classBeforeVCapBody c)).regs 131 ≤ 1 := by
  let before := arun k s (classBeforeSelectorBody c)
  have hlarge := classBeforeSelector_large_le_one c k s
  have hactiveBefore : before.regs 9 ≤ 1 := by
    rw [arun_frame k 9 (classBeforeSelectorBody c) (by rfl) s]
    exact hactive
  let selected := arun k before (classSelectBody c)
  have hpush := classSelectBody_push_le_one c k before hlarge hactiveBefore
  have hbit := classCapPrep_bit_le_one c k selected hpush
  rw [classBeforeVCapBody_eq_stages, arun_append, arun_append]
  exact hbit

/-- The unique capacity-counter instruction performs ordinary addition when
the explicit room premise rules out word wrap. -/
theorem classVCapCommitBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (hroom : s.regs rVCap + s.regs 131 < M) :
    (arun k s (classVCapCommitBody c)).regs rVCap =
      s.regs rVCap + s.regs 131 := by
  have hroom' : s.regs 354 + s.regs 131 < M := by
    simpa [rVCap] using hroom
  simp [classVCapCommitBody, R2Cfg.classBody, arun, astep,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp, rVCap,
    Nat.mod_eq_of_lt hroom']

/-- One complete scheduled body adds exactly its literal capacity-failure bit.
Every other compiled instruction frames `rVCap`. -/
theorem body_vcap_increment (c : R2Cfg) (k : Nat) (s : AState)
    (hroom :
      let marked := arun k s c.markBody
      let before := arun k marked (classBeforeVCapBody c)
      s.regs rVCap + before.regs 131 < M) :
    let marked := arun k s c.markBody
    let before := arun k marked (classBeforeVCapBody c)
    (arun k s c.body).regs rVCap = s.regs rVCap + before.regs 131 := by
  let marked := arun k s c.markBody
  have hmarkFrame : marked.regs rVCap = s.regs rVCap :=
    arun_frame k rVCap c.markBody (by rfl) s
  let before := arun k marked (classBeforeVCapBody c)
  have hbeforeFrame : before.regs rVCap = s.regs rVCap :=
    (arun_frame k rVCap (classBeforeVCapBody c) (by rfl) marked).trans
      hmarkFrame
  let committed := arun k before (classVCapCommitBody c)
  have hcommit := classVCapCommitBody_run c k before (by
    rw [hbeforeFrame]
    exact hroom)
  have hsuffix :
      (arun k committed
          (classAfterVCapBody c ++ c.logBody ++ c.tailBody)).regs rVCap =
        committed.regs rVCap :=
    arun_frame k rVCap
      (classAfterVCapBody c ++ c.logBody ++ c.tailBody) (by rfl) committed
  rw [R2Cfg.body, classBody_eq_vcap_stages, arun_append, arun_append,
    arun_append, arun_append, arun_append]
  rw [hbeforeFrame] at hcommit
  exact hsuffix.trans hcommit

/-- Exact compiled capacity bit associated with one scheduled body. -/
def bodyCapBit (c : R2Cfg) (k : Nat) (s : AState) : Nat :=
  let marked := arun k s c.markBody
  let before := arun k marked (classBeforeVCapBody c)
  before.regs 131

theorem bodyCapBit_le_one (c : R2Cfg) (k : Nat) (s : AState)
    (hTL : c.markSteps + c.segLen < M) :
    bodyCapBit c k s ≤ 1 := by
  let marked := arun k s c.markBody
  have hactive := markBody_class_active_le_one c k s hTL
  exact classBeforeVCap_bit_le_one c k marked hactive

/-- Across an arbitrary scheduled list, `rVCap` is monotone and grows by at
most one per body. -/
theorem foldl_body_vcap_bounds (c : R2Cfg) (indices : List Nat) (s : AState)
    (hTL : c.markSteps + c.segLen < M)
    (hroom : s.regs rVCap + indices.length < M) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    s.regs rVCap ≤ out.regs rVCap ∧
      out.regs rVCap ≤ s.regs rVCap + indices.length := by
  induction indices generalizing s with
  | nil => simp
  | cons k ks ih =>
      let bit := bodyCapBit c k s
      have hbit : bit ≤ 1 := bodyCapBit_le_one c k s hTL
      have hfirstRoom : s.regs rVCap + bit < M := by
        simp only [List.length_cons] at hroom
        omega
      have hfirst := body_vcap_increment c k s (by
        simpa only [bodyCapBit, bit] using hfirstRoom)
      change (arun k s c.body).regs rVCap = s.regs rVCap + bit at hfirst
      have htailRoom :
          (arun k s c.body).regs rVCap + ks.length < M := by
        rw [hfirst]
        simp only [List.length_cons] at hroom
        omega
      have htail := ih (s := arun k s c.body) htailRoom
      dsimp only at htail
      simp only [List.foldl]
      constructor
      · calc
          s.regs rVCap ≤ s.regs rVCap + bit := Nat.le_add_right _ _
          _ = (arun k s c.body).regs rVCap := hfirst.symm
          _ ≤ _ := htail.1
      · calc
          (ks.foldl (fun st k => arun k st c.body)
              (arun k s c.body)).regs rVCap
              ≤ (arun k s c.body).regs rVCap + ks.length := htail.2
          _ = s.regs rVCap + bit + ks.length := by rw [hfirst]
          _ ≤ s.regs rVCap + (ks.length + 1) := by omega

theorem runtimeProductionEntry_vcap_zero :
    runtimeProductionEntry.regs rVCap = 0 := by
  have hframe := arun_frame 0 rVCap
    (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).init
    (by rfl)
    (initialAStateWithArray runtimeProductionPacked.arr)
  rw [runtimeProductionEntry, hframe]
  rfl

/-- Every dynamic invocation of the literal stream-capacity guard passed in
the retained production execution. -/
theorem runtimeProduction_every_capacity_guard_passes :
    ∀ j, j < runtimeProductionCfg.period * runtimeProductionCfg.segCount →
      bodyCapBit runtimeProductionCfg j (runtimeProductionPrefix j) = 0 := by
  intro j hj
  let c := runtimeProductionCfg
  let N := c.period * c.segCount
  let pre := runtimeProductionPrefix j
  let bit := bodyCapBit c j pre
  let after := arun j pre c.body
  change j < N at hj
  have hentry : runtimeProductionEntry.regs rVCap = 0 :=
    runtimeProductionEntry_vcap_zero
  have hNM : N < M := by
    dsimp only [N, c]
    decide
  have hpreBounds := foldl_body_vcap_bounds c (List.range j)
    runtimeProductionEntry (by decide) (by
      rw [hentry]
      simp only [List.length_range, Nat.zero_add]
      omega)
  have hpreLe : pre.regs rVCap ≤ j := by
    simpa only [pre, runtimeProductionPrefix, bodyPrefix, c,
      List.length_range, hentry, Nat.zero_add] using hpreBounds.2
  have hbitLe : bit ≤ 1 := bodyCapBit_le_one c j pre (by decide)
  have hfirstRoom : pre.regs rVCap + bit < M := by omega
  have hfirst := body_vcap_increment c j pre (by
    simpa only [bodyCapBit, bit] using hfirstRoom)
  change after.regs rVCap = pre.regs rVCap + bit at hfirst
  have hafterLe : after.regs rVCap ≤ j + 1 := by omega
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
  have htailRoom : after.regs rVCap + tail.length < M := by
    have htailLength : tail.length = tailLen := by simp [tail]
    rw [htailLength]
    omega
  have htailBounds := foldl_body_vcap_bounds c tail after (by decide)
    htailRoom
  dsimp only at htailBounds
  have hloopZero := runtimeProduction_verified_no_mark_or_drain_failure.2.1
  rw [runtimeProductionLoopOut_eq_fold] at hloopZero
  have hloopZero' :
    ((List.range N).foldl (fun s index => arun index s c.body)
      runtimeProductionEntry).regs rVCap = 0 := by
    simpa only [N, c] using hloopZero
  rw [hrange, List.foldl_append] at hloopZero'
  change
    (tail.foldl (fun s index => arun index s c.body) after).regs rVCap = 0
      at hloopZero'
  have hafterZero : after.regs rVCap = 0 := by omega
  change bit = 0
  omega

#print axioms markBody_class_active_le_one
#print axioms classBeforeVCap_bit_le_one
#print axioms body_vcap_increment
#print axioms foldl_body_vcap_bounds
#print axioms runtimeProduction_every_capacity_guard_passes

end LeanCompCert.Ports.R2SegSieve

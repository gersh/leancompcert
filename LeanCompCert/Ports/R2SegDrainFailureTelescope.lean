import LeanCompCert.Ports.R2SegMarkFailureTelescope

/-!
# Telescope for the compiled R2 stream-drain failure counter

The production body has exactly one writer of `rVDrain`: instruction ten of
`tailBody`.  This file isolates that writer, proves that its increment is a
Boolean word, and transports the terminal zero in the retained compiled run
back to every scheduled invocation.  The production fold is never evaluated
by Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve

set_option maxRecDepth 20000

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.InstrBlock

/-- Literal tail prefix through the shared failure-counter update, immediately
before the independent `rVDrain` update. -/
def tailBeforeVDrainBody (c : R2Cfg) : List AInstr := c.tailBody.take 9

/-- The unique instruction writing `rVDrain`. -/
def tailVDrainCommitBody (c : R2Cfg) : List AInstr :=
  (c.tailBody.drop 9).take 1

/-- Literal tail suffix after the unique `rVDrain` write. -/
def tailAfterVDrainBody (c : R2Cfg) : List AInstr := c.tailBody.drop 10

theorem tailBody_eq_vdrain_stages (c : R2Cfg) :
    c.tailBody = tailBeforeVDrainBody c ++ tailVDrainCommitBody c ++
      tailAfterVDrainBody c := by
  rfl

/-- The compiled drain predicate is the product of two comparison bits. -/
theorem tailBeforeVDrain_bit_le_one (c : R2Cfg) (k : Nat) (s : AState) :
    (arun k s (tailBeforeVDrainBody c)).regs 335 ≤ 1 := by
  simp [tailBeforeVDrainBody, R2Cfg.tailBody, arun, astep,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp,
    rR, rW, rEc, rWc, rViol]
  split <;> split <;> simp [M]

/-- The unique drain-counter instruction performs ordinary addition whenever
the explicit room premise rules out word wrap. -/
theorem tailVDrainCommitBody_run (c : R2Cfg) (k : Nat) (s : AState)
    (hroom : s.regs rVDrain + s.regs 335 < M) :
    (arun k s (tailVDrainCommitBody c)).regs rVDrain =
      s.regs rVDrain + s.regs 335 := by
  have hroom' : s.regs 355 + s.regs 335 < M := by
    simpa [rVDrain] using hroom
  simp [tailVDrainCommitBody, R2Cfg.tailBody, arun, astep,
    AState.writeReg, sdest, sval, denoteOperand, denoteOp, rVDrain,
    Nat.mod_eq_of_lt hroom']

/-- One complete scheduled body adds exactly its compiled drain-failure bit.
Every earlier phase and the remaining tail instructions frame `rVDrain`. -/
theorem body_vdrain_increment (c : R2Cfg) (k : Nat) (s : AState)
    (hroom :
      let beforeTail := arun k s (c.markBody ++ c.classBody ++ c.logBody)
      let before := arun k beforeTail (tailBeforeVDrainBody c)
      s.regs rVDrain + before.regs 335 < M) :
    let beforeTail := arun k s (c.markBody ++ c.classBody ++ c.logBody)
    let before := arun k beforeTail (tailBeforeVDrainBody c)
    (arun k s c.body).regs rVDrain =
      s.regs rVDrain + before.regs 335 := by
  let beforeTail := arun k s (c.markBody ++ c.classBody ++ c.logBody)
  let before := arun k beforeTail (tailBeforeVDrainBody c)
  have hprefixFrame : beforeTail.regs rVDrain = s.regs rVDrain :=
    arun_frame k rVDrain (c.markBody ++ c.classBody ++ c.logBody)
      (by rfl) s
  have hbeforeFrame : before.regs rVDrain = s.regs rVDrain :=
    (arun_frame k rVDrain (tailBeforeVDrainBody c) (by rfl)
      beforeTail).trans hprefixFrame
  let committed := arun k before (tailVDrainCommitBody c)
  have hcommit := tailVDrainCommitBody_run c k before (by
    rw [hbeforeFrame]
    exact hroom)
  have hsuffix :
      (arun k committed (tailAfterVDrainBody c)).regs rVDrain =
        committed.regs rVDrain :=
    arun_frame k rVDrain (tailAfterVDrainBody c) (by rfl) committed
  rw [R2Cfg.body, tailBody_eq_vdrain_stages, arun_append, arun_append,
    arun_append, arun_append]
  rw [hbeforeFrame] at hcommit
  exact hsuffix.trans hcommit

/-- The exact compiled drain bit associated with one scheduled body. -/
def bodyDrainBit (c : R2Cfg) (k : Nat) (s : AState) : Nat :=
  let beforeTail := arun k s (c.markBody ++ c.classBody ++ c.logBody)
  let before := arun k beforeTail (tailBeforeVDrainBody c)
  before.regs 335

theorem bodyDrainBit_le_one (c : R2Cfg) (k : Nat) (s : AState) :
    bodyDrainBit c k s ≤ 1 := by
  exact tailBeforeVDrain_bit_le_one c k _

/-- Across an arbitrary list of scheduled bodies, `rVDrain` grows
monotonically and by at most one per iteration. -/
theorem foldl_body_vdrain_bounds (c : R2Cfg) (indices : List Nat) (s : AState)
    (hroom : s.regs rVDrain + indices.length < M) :
    let out := indices.foldl (fun st k => arun k st c.body) s
    s.regs rVDrain ≤ out.regs rVDrain ∧
      out.regs rVDrain ≤ s.regs rVDrain + indices.length := by
  induction indices generalizing s with
  | nil => simp
  | cons k ks ih =>
      let bit := bodyDrainBit c k s
      have hbit : bit ≤ 1 := bodyDrainBit_le_one c k s
      have hfirstRoom : s.regs rVDrain + bit < M := by
        simp only [List.length_cons] at hroom
        omega
      have hfirst := body_vdrain_increment c k s (by
        simpa only [bodyDrainBit, bit] using hfirstRoom)
      change (arun k s c.body).regs rVDrain = s.regs rVDrain + bit at hfirst
      have htailRoom :
          (arun k s c.body).regs rVDrain + ks.length < M := by
        rw [hfirst]
        simp only [List.length_cons] at hroom
        omega
      have htail := ih (s := arun k s c.body) htailRoom
      dsimp only at htail
      simp only [List.foldl]
      constructor
      · calc
          s.regs rVDrain ≤ s.regs rVDrain + bit := Nat.le_add_right _ _
          _ = (arun k s c.body).regs rVDrain := hfirst.symm
          _ ≤ _ := htail.1
      · calc
          (ks.foldl (fun st k => arun k st c.body)
              (arun k s c.body)).regs rVDrain
              ≤ (arun k s c.body).regs rVDrain + ks.length := htail.2
          _ = s.regs rVDrain + bit + ks.length := by rw [hfirst]
          _ ≤ s.regs rVDrain + (ks.length + 1) := by omega

theorem runtimeProductionEntry_vdrain_zero :
    runtimeProductionEntry.regs rVDrain = 0 := by
  have hframe := arun_frame 0 rVDrain
    (r2RuntimeProgram runtimeProductionCfg runtimeProductionSeed).init
    (by rfl)
    (initialAStateWithArray runtimeProductionPacked.arr)
  rw [runtimeProductionEntry, hframe]
  rfl

/-- Every dynamic invocation of the literal drain guard passed in the retained
production execution. -/
theorem runtimeProduction_every_drain_guard_passes :
    ∀ j, j < runtimeProductionCfg.period * runtimeProductionCfg.segCount →
      bodyDrainBit runtimeProductionCfg j (runtimeProductionPrefix j) = 0 := by
  intro j hj
  let c := runtimeProductionCfg
  let N := c.period * c.segCount
  let pre := runtimeProductionPrefix j
  let bit := bodyDrainBit c j pre
  let after := arun j pre c.body
  change j < N at hj
  have hentry : runtimeProductionEntry.regs rVDrain = 0 :=
    runtimeProductionEntry_vdrain_zero
  have hNM : N < M := by
    dsimp only [N, c]
    decide
  have hpreBounds := foldl_body_vdrain_bounds c (List.range j)
    runtimeProductionEntry (by
      rw [hentry]
      simp only [List.length_range, Nat.zero_add]
      omega)
  have hpreLe : pre.regs rVDrain ≤ j := by
    simpa only [pre, runtimeProductionPrefix, bodyPrefix, c,
      List.length_range, hentry, Nat.zero_add] using hpreBounds.2
  have hbitLe : bit ≤ 1 := bodyDrainBit_le_one c j pre
  have hfirstRoom : pre.regs rVDrain + bit < M := by omega
  have hfirst := body_vdrain_increment c j pre (by
    simpa only [bodyDrainBit, bit] using hfirstRoom)
  change after.regs rVDrain = pre.regs rVDrain + bit at hfirst
  have hafterLe : after.regs rVDrain ≤ j + 1 := by omega
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
  have htailRoom : after.regs rVDrain + tail.length < M := by
    have htailLength : tail.length = tailLen := by simp [tail]
    rw [htailLength]
    omega
  have htailBounds := foldl_body_vdrain_bounds c tail after htailRoom
  dsimp only at htailBounds
  have hloopZero := runtimeProduction_verified_no_mark_or_drain_failure.2.2
  rw [runtimeProductionLoopOut_eq_fold] at hloopZero
  have hloopZero' :
    ((List.range N).foldl (fun s index => arun index s c.body)
      runtimeProductionEntry).regs rVDrain = 0 := by
    simpa only [N, c] using hloopZero
  rw [hrange, List.foldl_append] at hloopZero'
  change
    (tail.foldl (fun s index => arun index s c.body) after).regs rVDrain = 0
      at hloopZero'
  have hafterZero : after.regs rVDrain = 0 := by omega
  change bit = 0
  omega

#print axioms tailBeforeVDrain_bit_le_one
#print axioms body_vdrain_increment
#print axioms foldl_body_vdrain_bounds
#print axioms runtimeProduction_every_drain_guard_passes

end LeanCompCert.Ports.R2SegSieve

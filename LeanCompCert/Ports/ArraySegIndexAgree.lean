/-
The segmented sieve's core body depends on the loop index only through two
phase selectors.
-/
import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Ports.CDEMAbelIndexIndependence
import LeanCompCert.Ports.ArraySegMobiusIndexedRun
import LeanCompCert.Ports.ArraySegMobiusCursorModel
import LeanCompCert.Ports.ArraySegMobiusIndexedSignal
import LeanCompCert.Ports.ArraySegMobiusSquaredSignal

/-!
# Index agreement for the segmented sieve's core body

Two run shapes appear in the segmented Möbius port and they disagree about the
loop index:

* `bodyRun idx c fuel s` iterates `arun idx` — the index is **fixed**, and it
  is what `readSig_windowRun_main_cell_eq_rootFoldValue` is stated against;
* `indexedBodyRun idx c fuel s` iterates `arun (idx + k)` — the index
  **advances**, and it is what `combinedSignals` reduces to.

Nothing composes the two, which is why the emitted-cell theorem cannot be fed
to the signal schedule directly.

They do agree, but not unconditionally: `Cfg.coreBody` reads `.idx` in exactly
two instructions, and both are phase selectors —

```
reg 130 ← idx < rootSpan        (in the root phase?)
reg 142 ← idx = rootSpan − 1     (the last root step?)
```

so any two indices that are **past the root span** and are **not the last root
step** drive the body identically.  Those are precisely the hypotheses
`hmain` and `hidxNe` that the emitted-cell theorem already carries, so the
agreement costs its consumer nothing.

⚠ The bound `i < M` is load-bearing on both sides: `.idx` denotes `idx % M`, so
without it two indices congruent mod `2^64` would compare equal to `rootSpan`
when only one of them is.

The general machinery — `ainstrIndexFree`, `astep_indexFree` — is
`CDEMAbelIndexIndependence`'s and is not sieve-specific.  What is specific is
the *pointwise* variant below: `arun_indexFree` needs the whole block index
free, and this block is not.
-/

namespace LeanCompCert.Ports.ArraySegIndexAgree

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.CDEMAbelIndexIndependence

/-- `arun_indexFree`, weakened from "every instruction is index free" to
"every instruction *agrees* at the two indices".  That is what a block with a
few index-dependent selectors needs. -/
theorem arun_agree (i j : Nat) : ∀ (block : List AInstr) (st : AState),
    (∀ (t : AState) (instr : AInstr), instr ∈ block →
      astep i t instr = astep j t instr) →
    arun i st block = arun j st block := by
  intro block
  induction block with
  | nil => intro st _; rfl
  | cons instr rest ih =>
      intro st h
      rw [arun_cons, arun_cons, h st instr (by simp)]
      exact ih _ (fun t x hx => h t x (by simp [hx]))

/-- **The core body's only index-dependent instructions.**  Structural, so it
holds for every configuration. -/
theorem coreBody_idx_instrs (c : Cfg) :
    c.coreBody.filter (fun x => !ainstrIndexFree x)
      = [ .scalar (.binop 130 .lt .idx (.lit c.rootSpan))
        , .scalar (.binop 142 .eq .idx (.lit (c.rootSpan - 1))) ] := rfl

/-- **Two main-phase indices drive the core body identically.** -/
theorem arun_coreBody_agree (c : Cfg) (i j : Nat) (st : AState)
    (hiM : i < M) (hjM : j < M) (hspanM : c.rootSpan < M)
    (hi : c.rootSpan ≤ i) (hj : c.rootSpan ≤ j)
    (hiNe : i ≠ c.rootSpan - 1) (hjNe : j ≠ c.rootSpan - 1) :
    arun i st c.coreBody = arun j st c.coreBody := by
  have hiMod : i % M = i := Nat.mod_eq_of_lt hiM
  have hjMod : j % M = j := Nat.mod_eq_of_lt hjM
  have hspanMod : c.rootSpan % M = c.rootSpan := Nat.mod_eq_of_lt hspanM
  have hspan1Mod : (c.rootSpan - 1) % M = c.rootSpan - 1 :=
    Nat.mod_eq_of_lt (by omega)
  refine arun_agree i j c.coreBody st (fun t instr hmem => ?_)
  by_cases hfree : ainstrIndexFree instr = true
  · exact astep_indexFree i j t instr hfree
  · have hmem' : instr ∈ c.coreBody.filter (fun x => !ainstrIndexFree x) := by
      refine List.mem_filter.mpr ⟨hmem, ?_⟩
      simpa using hfree
    rw [coreBody_idx_instrs] at hmem'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
    rcases hmem' with rfl | rfl <;>
      simp only [astep, LeanCompCert.Verified.InstrBlock.sdest,
        LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
        Option.getD_some, hiMod, hjMod, hspanMod, hspan1Mod]
    · rw [if_neg (by omega), if_neg (by omega)]
    · rw [if_neg hiNe, if_neg hjNe]

open LeanCompCert.Ports.ArraySegMobiusIndexedRun in
open LeanCompCert.Ports.ArraySegMobiusCursorModel in
/-- **The two run shapes coincide in the main phase.**  This is the step that
lets an emitted-cell theorem stated with a fixed index be fed to a signal
schedule that advances one. -/
theorem indexedBodyRun_eq_bodyRun (c : Cfg) (idx : Nat)
    (hspanM : c.rootSpan < M) (hi : c.rootSpan ≤ idx)
    (hiNe : idx ≠ c.rootSpan - 1) :
    ∀ (fuel : Nat), idx + fuel < M → ∀ st : AState,
      indexedBodyRun idx c fuel st = bodyRun idx c fuel st := by
  intro fuel
  induction fuel with
  | zero => intro _ st; rfl
  | succ fuel ih =>
      intro hlt st
      have hprev : indexedBodyRun idx c fuel st = bodyRun idx c fuel st :=
        ih (by omega) st
      rw [indexedBodyRun_succ, bodyRun_succ, hprev]
      refine arun_coreBody_agree c (idx + fuel) idx _ (by omega) (by omega)
        hspanM (by omega) hi (by omega) hiNe

open LeanCompCert.Ports.ArraySegMobiusIndexedRun in
open LeanCompCert.Ports.ArraySegMobiusCursorModel in
open LeanCompCert.Ports.ArraySegMobiusIndexedSignal in
open LeanCompCert.Ports.ArraySegMobiusResidueFold in
open LeanCompCert.Ports.ArraySegMobiusResidueFrame in
open LeanCompCert.Ports.ArraySegMobiusSquaredFold in
open LeanCompCert.Ports.ArraySegMobiusSquaredSignal in
open LeanCompCert.Ports.MobiusResidueRealisation in
/-- **The main phase's emitted signals are the mathematical schedule.**

The root phase (`combinedSignals_root_schedule`) and the marking phase
(`combinedSignals_main_mark_schedule`) are already known idle; this is the
third and last one, and the only one that carries information.

`hcell` is the emitted-cell equation — `readSig_windowRun_main_cell_eq_rootFoldValue`'s
conclusion — taken as a hypothesis rather than restated with its twenty-one
side conditions about table, budget and cursor.  Everything between it and the
schedule is the index bookkeeping proved above. -/
theorem combinedSignals_main_active_schedule
    (mu : Nat → Int) (lo idx : Nat) (c : Cfg) (k : Nat)
    (combined core : AState)
    (hagree : CoreAgree combined core)
    (hspanM : c.rootSpan < M) (hmain : c.rootSpan ≤ idx)
    (hspanPos : 0 < c.rootSpan) (hidxM : idx + c.segLen < M)
    (hcell : ∀ i, i < c.segLen →
      readSig (arun idx (bodyRun idx c i core) c.coreBody)
        = muSig mu (lo + i + 1)) :
    ConsecutiveSignalSchedule mu lo
      (combinedSignals idx c k c.segLen combined) c.segLen := by
  have hidxNe : idx ≠ c.rootSpan - 1 := by omega
  refine combinedSignals_schedule_of_active mu lo idx c k c.segLen combined
    (fun j hj => ?_)
  rw [readSig_combinedIndexedRun_eq_indexedBodyRun idx c k j hagree,
    indexedBodyRun_eq_bodyRun c idx hspanM hmain hidxNe j (by omega) core,
    arun_coreBody_agree c (idx + j) idx (bodyRun idx c j core)
      (by omega) (by omega) hspanM (by omega) hmain (by omega) hidxNe]
  exact hcell j hj

open LeanCompCert.Ports.ArraySegMobiusResidueFold in
open LeanCompCert.Ports.ArraySegMobiusSquaredFold in
open LeanCompCert.Ports.MobiusResidueRealisation in
/-- **One window's schedule**: marking (idle) followed by the main segment.
Both halves are taken as hypotheses so this composes with whichever phase
theorem a caller has. -/
theorem combinedSignals_window_schedule
    (mu : Nat → Int) (lo idx : Nat) (c : Cfg) (k : Nat) (s : AState)
    (hmark : ConsecutiveSignalSchedule mu lo
      (combinedSignals idx c k c.markSteps s) 0)
    (hmain : ConsecutiveSignalSchedule mu lo
      (combinedSignals (idx + c.markSteps) c k c.segLen
        (combinedIndexedRun idx c k c.markSteps s)) c.segLen) :
    ConsecutiveSignalSchedule mu lo
      (combinedSignals idx c k (c.markSteps + c.segLen) s) c.segLen := by
  rw [combinedSignals_add]
  simpa using ConsecutiveSignalSchedule.append hmark (by simpa using hmain)

open LeanCompCert.Ports.ArraySegMobiusResidueFold in
open LeanCompCert.Ports.ArraySegMobiusSquaredFold in
open LeanCompCert.Ports.MobiusResidueRealisation in
/-- **Many windows.**  The whole main run is `W` windows of `markSteps +
segLen` steps, contributing `segLen` mathematical points each.  This is the
shape a sharded sweep needs: the count is a parameter, not eight cases.

⚠ Window `t` starts at mathematical prefix `lo + t·segLen`, not `lo` — the
marking steps advance the machine but not the mathematics, which is exactly
what `hmark`'s count of `0` records. -/
theorem combinedSignals_windows_schedule
    (mu : Nat → Int) (lo idx : Nat) (c : Cfg) (k : Nat) :
    ∀ (W : Nat) (s : AState),
      (∀ t, t < W →
        ConsecutiveSignalSchedule mu (lo + t * c.segLen)
          (combinedSignals (idx + t * (c.markSteps + c.segLen)) c k
            (c.markSteps + c.segLen)
            (combinedIndexedRun idx c k (t * (c.markSteps + c.segLen)) s))
          c.segLen) →
      ConsecutiveSignalSchedule mu lo
        (combinedSignals idx c k (W * (c.markSteps + c.segLen)) s)
        (W * c.segLen) := by
  intro W
  induction W with
  | zero =>
      intro s _
      rw [Nat.zero_mul, Nat.zero_mul,
        show combinedSignals idx c k 0 s = [] from by simp [combinedSignals]]
      exact ConsecutiveSignalSchedule.nil lo
  | succ W ih =>
      intro s h
      have hsplit : (W + 1) * (c.markSteps + c.segLen)
          = W * (c.markSteps + c.segLen) + (c.markSteps + c.segLen) :=
        Nat.succ_mul W (c.markSteps + c.segLen)
      have harith : (W + 1) * c.segLen = W * c.segLen + c.segLen :=
        Nat.succ_mul W c.segLen
      rw [hsplit, combinedSignals_add, harith]
      exact ConsecutiveSignalSchedule.append (ih s (fun t ht => h t (by omega)))
        (h W (by omega))

#print axioms combinedSignals_window_schedule
#print axioms combinedSignals_windows_schedule

#print axioms combinedSignals_main_active_schedule

#print axioms indexedBodyRun_eq_bodyRun

#print axioms arun_agree
#print axioms coreBody_idx_instrs
#print axioms arun_coreBody_agree

end LeanCompCert.Ports.ArraySegIndexAgree

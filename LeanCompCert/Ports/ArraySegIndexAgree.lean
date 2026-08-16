/-
The segmented sieve's core body depends on the loop index only through two
phase selectors.
-/
import LeanCompCert.Ports.ArraySegSieve
import LeanCompCert.Ports.CDEMAbelIndexIndependence
import LeanCompCert.Ports.ArraySegMobiusIndexedRun
import LeanCompCert.Ports.ArraySegMobiusCursorModel

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

#print axioms indexedBodyRun_eq_bodyRun

#print axioms arun_agree
#print axioms coreBody_idx_instrs
#print axioms arun_coreBody_agree

end LeanCompCert.Ports.ArraySegIndexAgree

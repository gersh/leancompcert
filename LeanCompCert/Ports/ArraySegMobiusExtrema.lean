import LeanCompCert.Ports.MobiusExtremaScalar
import LeanCompCert.Ports.ArraySegMobiusIndexedSignal
import LeanCompCert.Verified.ArrayScalarBlock

/-!
# Array-machine semantics of the Platt (2.11) extrema residue

`ArraySegSieve.mobiusOverNResidue` is the literal nineteen-instruction suffix
used by every window of the completed production campaign. Its scalar
semantics were already proved in `MobiusExtremaScalar`; this leaf transports
that result back to the array machine without expanding an array state through
nineteen scalar instructions.

The only source-definedness premise is the paper candidate's nonzeroness. No
compiled receipt is reversed to obtain it.
-/

namespace LeanCompCert.Ports.ArraySegMobiusExtrema

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayScalarBlock
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusSignal
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusIndexedRun
open LeanCompCert.Ports.ArraySegMobiusIndexedSignal
open LeanCompCert.Ports.MobiusResidueRealisation

/-- The three persistent extrema fields as read from an array-machine state. -/
def readExt (s : AState) : MobiusExtremaScalar.Ext :=
  MobiusExtremaScalar.readExt s.regs

/-- The production array residue is literally the lifted scalar residue. -/
theorem residue_eq_lift :
    mobiusOverNResidue = lift MobiusExtremaScalar.residue := by
  exact MobiusExtremaScalar.residue_map_scalar.symm

/-- Total execution of the literal array residue is the exact transparent
extrema transition. -/
theorem readExt_arun (idx : Nat) (s : AState) (hn : s.regs 65 ≠ 0) :
    readExt (arun idx s mobiusOverNResidue) =
      MobiusExtremaScalar.extStep
        (MobiusResidueScalar.readSig s.regs) (readExt s) := by
  rw [residue_eq_lift]
  unfold readExt
  rw [arun_lift_regs]
  exact MobiusExtremaScalar.readExt_srun idx s.regs hn

/-- The scalar suffix never changes the segmented sieve's arrays. -/
theorem arun_arr (idx : Nat) (s : AState) :
    (arun idx s mobiusOverNResidue).arr = s.arr := by
  rw [residue_eq_lift, arun_lift_arr]

private theorem residue_avoids_core (j : Nat) (hj : CoreReg j = true) :
    mobiusOverNResidue.all (avoidsReg j) = true := by
  have hw : ¬((100 ≤ j ∧ j ≤ 120) ∨ (150 ≤ j ∧ j ≤ 191)) :=
    of_decide_eq_true hj
  have h100 : j < 100 ∨ 120 < j := by
    by_cases h : j < 100
    · exact Or.inl h
    · refine Or.inr (Nat.lt_of_not_ge ?_)
      intro hj120
      exact hw (Or.inl ⟨Nat.le_of_not_gt h, hj120⟩)
  simp [mobiusOverNResidue, avoidsReg, rT, rTmax, rTmin]
  rcases h100 with h100 | h100 <;> omega

/-- The extrema suffix leaves the complete sieve-facing projection intact. -/
theorem arun_core_frame (idx : Nat) (s : AState) :
    CoreAgree (arun idx s mobiusOverNResidue) s := by
  constructor
  · exact arun_arr idx s
  · intro j hj
    exact arun_reg_frame idx j mobiusOverNResidue s
      (residue_avoids_core j hj)

private theorem mobiusInit_avoids_core (t j : Nat)
    (hj : CoreReg j = true) :
    (mobiusInit t).all (avoidsReg j) = true := by
  have hw : ¬((100 ≤ j ∧ j ≤ 120) ∨ (150 ≤ j ∧ j ≤ 191)) :=
    of_decide_eq_true hj
  have h150 : j < 150 ∨ 191 < j := by
    by_cases h : j < 150
    · exact Or.inl h
    · refine Or.inr (Nat.lt_of_not_ge ?_)
      intro hj191
      exact hw (Or.inr ⟨Nat.le_of_not_gt h, hj191⟩)
  simp [mobiusInit, seed, avoidsReg, rT, rTmax, rTmin]
  rcases h150 with h150 | h150 <;> omega

/-- The historical extrema initializer changes only private scalar fields. -/
theorem arun_mobiusInit_core_frame (t idx : Nat) (s : AState) :
    CoreAgree (arun idx s (mobiusInit t)) s := by
  constructor
  · exact arun_arr_frame idx (mobiusInit t) s (by rfl)
  · intro j hj
    exact arun_reg_frame idx j (mobiusInit t) s
      (mobiusInit_avoids_core t j hj)

/-- One core-plus-extrema event projects to the ordinary standalone core. -/
theorem arun_combined_core (c : Cfg) (idx : Nat) {s t : AState}
    (h : CoreAgree s t) :
    CoreAgree (arun idx s (c.coreBody ++ mobiusOverNResidue))
      (arun idx t c.coreBody) := by
  rw [arun_append]
  exact (arun_core_frame idx (arun idx s c.coreBody)).trans
    (arun_coreBody_congr c idx h)

/-- Actual changing-index execution of the production extrema body. -/
def combinedIndexedRun (idx : Nat) (c : Cfg) : Nat → AState → AState
  | 0, s => s
  | fuel + 1, s =>
      arun (idx + fuel) (combinedIndexedRun idx c fuel s)
        (c.coreBody ++ mobiusOverNResidue)

@[simp] theorem combinedIndexedRun_zero (idx : Nat) (c : Cfg) (s : AState) :
    combinedIndexedRun idx c 0 s = s := rfl

@[simp] theorem combinedIndexedRun_succ (idx : Nat) (c : Cfg) (fuel : Nat)
    (s : AState) :
    combinedIndexedRun idx c (fuel + 1) s =
      arun (idx + fuel) (combinedIndexedRun idx c fuel s)
        (c.coreBody ++ mobiusOverNResidue) := rfl

/-- Split the literal extrema trace at an arbitrary finite event boundary. -/
theorem combinedIndexedRun_add (idx : Nat) (c : Cfg) (a b : Nat)
    (s : AState) :
    combinedIndexedRun idx c (a + b) s =
      combinedIndexedRun (idx + a) c b
        (combinedIndexedRun idx c a s) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Nat.add_succ, combinedIndexedRun_succ, combinedIndexedRun_succ, ih]
      have heq : idx + (a + b) = idx + a + b := by omega
      rw [heq]

/-- The complete extrema trace retains exactly the standalone indexed sieve
trace in its core-facing projection. -/
theorem combinedIndexedRun_core (idx : Nat) (c : Cfg) (fuel : Nat)
    {s t : AState} (h : CoreAgree s t) :
    CoreAgree (combinedIndexedRun idx c fuel s)
      (indexedBodyRun idx c fuel t) := by
  induction fuel with
  | zero => exact h
  | succ n ih =>
      rw [combinedIndexedRun_succ, indexedBodyRun_succ]
      exact arun_combined_core c (idx + n) ih

/-- The recursive combined runner is the literal fold used by `AProgram`. -/
theorem foldl_range_combined_eq_combinedIndexedRun (idx : Nat) (c : Cfg)
    (fuel : Nat) (s : AState) :
    (List.range fuel).foldl
        (fun q k => arun (idx + k) q (c.coreBody ++ mobiusOverNResidue)) s =
      combinedIndexedRun idx c fuel s := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih]
      rfl

/-- The complete historical core-plus-extrema trace has the standalone
verified sieve trace as its exact core-facing projection. -/
theorem historicalCombinedFold_core (c : Cfg) (t fuel : Nat) :
    let entry := arun 0 initialAState (c.coreInit ++ mobiusInit t)
    let full := (List.range fuel).foldl
      (fun q idx => arun idx q (c.coreBody ++ mobiusOverNResidue)) entry
    CoreAgree full
      (indexedBodyRun 0 c fuel (arun 0 initialAState c.coreInit)) := by
  dsimp only
  have hentry : CoreAgree
      (arun 0 initialAState (c.coreInit ++ mobiusInit t))
      (arun 0 initialAState c.coreInit) := by
    rw [arun_append]
    exact arun_mobiusInit_core_frame t 0
      (arun 0 initialAState c.coreInit)
  have hfold := foldl_range_combined_eq_combinedIndexedRun 0 c fuel
    (arun 0 initialAState (c.coreInit ++ mobiusInit t))
  simp only [Nat.zero_add] at hfold
  rw [hfold]
  exact combinedIndexedRun_core 0 c fuel hentry

/-- At every event the extrema trace presents exactly the signal of the
already-verified standalone segmented sieve trace. -/
theorem readSig_combined_eq_indexed (idx : Nat) (c : Cfg) (fuel : Nat)
    {s t : AState} (h : CoreAgree s t) :
    readSig (arun (idx + fuel) (combinedIndexedRun idx c fuel s) c.coreBody) =
      readSig (arun (idx + fuel) (indexedBodyRun idx c fuel t) c.coreBody) := by
  exact CoreAgree.readSig_eq
    (arun_coreBody_congr c (idx + fuel)
      (combinedIndexedRun_core idx c fuel h))

/-- The exact finite signal list consumed by an extrema trace. -/
def combinedSignals (idx : Nat) (c : Cfg) (fuel : Nat) (s : AState) :
    List Sig :=
  (List.range fuel).map fun j =>
    readSig (arun (idx + j) (combinedIndexedRun idx c j s) c.coreBody)

/- The exact extrema signal trace splits at the same finite event boundary. -/
set_option maxRecDepth 10000 in
theorem combinedSignals_add (idx : Nat) (c : Cfg) (a b : Nat)
    (s : AState) :
    combinedSignals idx c (a + b) s =
      combinedSignals idx c a s ++
        combinedSignals (idx + a) c b (combinedIndexedRun idx c a s) := by
  unfold combinedSignals
  rw [List.range_add, List.map_append, List.map_map]
  let pre : List Sig := (List.range a).map fun j =>
    readSig (arun (idx + j) (combinedIndexedRun idx c j s) c.coreBody)
  refine congrArg (fun tail : List Sig => pre ++ tail) ?_
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply]
  have hidx : idx + (a + j) = idx + a + j := (Nat.add_assoc idx a j).symm
  have hstate := combinedIndexedRun_add idx c a j s
  have hi := congrArg (fun index =>
    arun index (combinedIndexedRun idx c (a + j) s) c.coreBody) hidx
  have hs := congrArg (fun state =>
    arun (idx + a + j) state c.coreBody) hstate
  exact congrArg readSig (hi.trans hs)

/-- Transparent iteration of the nineteen-instruction extrema transition. -/
def extFold : List Sig → MobiusExtremaScalar.Ext → MobiusExtremaScalar.Ext
  | [], e => e
  | g :: gs, e => extFold gs (MobiusExtremaScalar.extStep g e)

theorem extFold_append (xs ys : List Sig) (e : MobiusExtremaScalar.Ext) :
    extFold (xs ++ ys) e = extFold ys (extFold xs e) := by
  induction xs generalizing e with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, extFold] using
        ih (MobiusExtremaScalar.extStep x e)

/-- The segmented core itself leaves all three persistent extrema fields
unchanged. -/
theorem readExt_arun_coreBody (c : Cfg) (idx : Nat) (s : AState) :
    readExt (arun idx s c.coreBody) = readExt s := by
  unfold readExt MobiusExtremaScalar.readExt
  congr 1

/-- One literal combined event advances exactly one transparent extrema
step, using the signal produced by that same core event. -/
theorem readExt_arun_combined (c : Cfg) (idx : Nat) (s : AState)
    (hn : (arun idx s c.coreBody).regs 65 ≠ 0) :
    readExt (arun idx s (c.coreBody ++ mobiusOverNResidue)) =
      MobiusExtremaScalar.extStep
        (readSig (arun idx s c.coreBody)) (readExt s) := by
  rw [arun_append, readExt_arun idx (arun idx s c.coreBody) hn,
    readExt_arun_coreBody]
  rfl

set_option maxRecDepth 10000 in
/-- The actual changing-index source trace is exactly the transparent fold
over its actual finite signal list. -/
theorem readExt_combinedIndexedRun_eq_extFold
    (idx : Nat) (c : Cfg) (fuel : Nat) (s : AState)
    (hready : ∀ j, j < fuel →
      (arun (idx + j) (combinedIndexedRun idx c j s) c.coreBody).regs 65 ≠ 0) :
    readExt (combinedIndexedRun idx c fuel s) =
      extFold (combinedSignals idx c fuel s) (readExt s) := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
      have hprev := ih (fun j hj => hready j (by omega))
      rw [combinedIndexedRun_succ,
        readExt_arun_combined c (idx + n)
          (combinedIndexedRun idx c n s)
          (hready n (Nat.lt_succ_self n)), hprev]
      simp only [combinedSignals, List.range_succ, List.map_append,
        extFold_append, List.map_singleton, extFold]

/-- The extrema trace consumes the same finite signal list as the standalone
indexed sieve trace from a core-agreeing entry. -/
theorem combinedSignals_eq_indexedSignals
    (idx : Nat) (c : Cfg) (fuel : Nat) {s t : AState}
    (h : CoreAgree s t) :
    combinedSignals idx c fuel s =
      (List.range fuel).map fun j =>
        readSig (arun (idx + j) (indexedBodyRun idx c j t) c.coreBody) := by
  unfold combinedSignals
  apply List.map_congr_left
  intro j hj
  exact readSig_combined_eq_indexed idx c j h

/-- The two literal divisions/remainders are defined exactly when the
candidate register is nonzero. -/
theorem residue_defined (len idx : Nat) (s : AState)
    (hn : s.regs 65 ≠ 0) :
    denoteAInstrs len idx s mobiusOverNResidue =
      some (arun idx s mobiusOverNResidue) := by
  apply denoteAInstrs_eq_arun
  rw [residue_eq_lift, allDefined_lift]
  simp [MobiusExtremaScalar.residue, MobiusResidueScalar.scalarOf,
    mobiusOverNResidue, LeanCompCert.Verified.InstrBlock.SAllDefined,
    LeanCompCert.Verified.InstrBlock.SDefined,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, denoteOp,
    RegState.set, hn]

/-- Successful partial denotation therefore has the same exact extrema
transition; this is the direction consumed by the production source trace. -/
theorem readExt_denote (len idx : Nat) (s out : AState)
    (hn : s.regs 65 ≠ 0)
    (h : denoteAInstrs len idx s mobiusOverNResidue = some out) :
    readExt out = MobiusExtremaScalar.extStep
      (MobiusResidueScalar.readSig s.regs) (readExt s) := by
  rw [residue_defined len idx s hn] at h
  cases h
  exact readExt_arun idx s hn

/-- The literal three-register initializer installs its modulo-word carry in
all three extrema fields. -/
theorem readExt_arun_mobiusInit (t idx : Nat) (s : AState) :
    readExt (arun idx s (mobiusInit t)) =
      ⟨t % M, t % M, t % M⟩ := by
  simp [readExt, MobiusExtremaScalar.readExt, mobiusInit, seed, arun, astep,
    AState.writeReg, LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, rT, rTmax, rTmin]

#print axioms readExt_arun
#print axioms residue_defined

end LeanCompCert.Ports.ArraySegMobiusExtrema

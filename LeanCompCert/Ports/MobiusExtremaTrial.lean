import LeanCompCert.Ports.MobiusExtremaScalar
import LeanCompCert.Ports.MobiusResidueTrial
import LeanCompCert.Verified.RegFrame

/-!
# Trial-division producer composed with the extrema residue

This is the slow, fully denoted fallback for Helfgott's `(2.11)` finite
computation.  `MobiusResidueTrial.signalBlock` exposes the result of the
proved `MertensCDEM` trial division, and `MobiusExtremaScalar.residue`
consumes that signal while maintaining `sum mu(n)/n` and its extrema.

The segmented sieve remains the practical producer.  This route is valuable
because it has no unproved sieve-to-signal refinement and can therefore serve
as a formally verified fallback and as the specification checked by faster
campaign artifacts.
-/

namespace LeanCompCert.Ports.MobiusExtremaTrial

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Ports.MertensCDEM
open LeanCompCert.Ports.MobiusResidueRealisation
open LeanCompCert.Ports.MobiusResidueTrial

set_option maxRecDepth 2048

/-- State after trial division and signal materialization, before the extrema
residue executes. -/
abbrev signalState := MobiusResidueTrial.signalState

/-- Trial-division body, signal materialization, and exact extrema residue. -/
def fullBody (c : Cfg) : List Instr :=
  body c ++ signalBlock c ++ MobiusExtremaScalar.residue

/-- Total state transformer corresponding to `fullBody`. -/
def fullStep (c : Cfg) (idx : Nat) (s : RegState) : RegState :=
  srun idx (signalState c idx s) MobiusExtremaScalar.residue

private theorem denoteInstrs_append_intro (idx : Nat) (s sm s' : RegState)
    (xs ys : List Instr)
    (hx : denoteInstrs idx s xs = some sm)
    (hy : denoteInstrs idx sm ys = some s') :
    denoteInstrs idx s (xs ++ ys) = some s' := by
  induction xs generalizing s sm with
  | nil =>
      simp only [denoteInstrs, Option.some.injEq] at hx
      subst sm
      exact hy
  | cons i rest ih =>
      simp only [List.cons_append, denoteInstrs] at hx ⊢
      cases hi : denoteInstr idx s i with
      | none => simp [hi] at hx
      | some sn =>
          simp only [hi] at hx ⊢
          exact ih sn sm hx hy

private theorem signalBlock_denote (c : Cfg) (idx : Nat) (s : RegState) :
    denoteInstrs idx s (signalBlock c) =
      some (srun idx s (signalBlock c)) := by
  apply srun_correct
  intro i hi
  simp only [signalBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

private theorem signalState_frame (c : Cfg) (idx r : Nat) (s : RegState)
    (hb : writes r (body c) = false)
    (hg : writes r (signalBlock c) = false) :
    signalState c idx s r = s r := by
  rw [signalState, MobiusResidueTrial.signalState,
    srun_frame idx r (signalBlock c) hg,
    step, srun_frame idx r (body c) hb]

/-- The producer leaves the three persistent extrema registers untouched. -/
theorem signalState_readExt (c : Cfg) (idx : Nat) (s : RegState) :
    MobiusExtremaScalar.readExt (signalState c idx s) =
      MobiusExtremaScalar.readExt s := by
  apply MobiusExtremaScalar.Ext.eq_of
  · exact signalState_frame c idx ArraySegSieve.rT s (by rfl) (by rfl)
  · exact signalState_frame c idx ArraySegSieve.rTmax s (by rfl) (by rfl)
  · exact signalState_frame c idx ArraySegSieve.rTmin s (by rfl) (by rfl)

/-- One complete denoted trial round.  Its only new partial operations divide
by the positive candidate in signal register 65. -/
theorem fullBody_denote (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hlo : 0 < c.lo) (hI : Inv s)
    (hidx : idx < c.len * c.rounds) :
    denoteInstrs idx s (fullBody c) = some (fullStep c idx s) := by
  have hb := body_denote c idx s hadm hI.1 hidx
  have hg := signalBlock_denote c idx (step c idx s)
  have hsig := signalState_readSig c idx s hadm hI hidx
  have hn : signalState c idx s 65 ≠ 0 := by
    have hn' := congrArg Sig.n hsig
    simp only [MobiusResidueScalar.readSig] at hn'
    have hnval : signalState c idx s 65 = c.lo + idx / c.rounds :=
      hn'.trans rfl
    rw [hnval]
    exact Nat.ne_of_gt (Nat.add_pos_left hlo _)
  have he := MobiusExtremaScalar.residue_defined idx (signalState c idx s) hn
  rw [fullBody, List.append_assoc]
  apply denoteInstrs_append_intro idx s (step c idx s)
      (fullStep c idx s) (body c)
      (signalBlock c ++ MobiusExtremaScalar.residue) hb
  apply denoteInstrs_append_intro idx (step c idx s)
      (signalState c idx s) (fullStep c idx s)
      (signalBlock c) MobiusExtremaScalar.residue hg
  exact he

/-- Reading the persistent fields after a round gives the exact extrema step
driven by that round's trial-derived signal. -/
theorem fullStep_readExt (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hlo : 0 < c.lo) (hI : Inv s)
    (hidx : idx < c.len * c.rounds) :
    MobiusExtremaScalar.readExt (fullStep c idx s) =
      MobiusExtremaScalar.extStep (roundSig c idx (obs s))
        (MobiusExtremaScalar.readExt s) := by
  have hsig := signalState_readSig c idx s hadm hI hidx
  have hn : signalState c idx s 65 ≠ 0 := by
    have hn' := congrArg Sig.n hsig
    simp only [MobiusResidueScalar.readSig] at hn'
    have hnval : signalState c idx s 65 = c.lo + idx / c.rounds :=
      hn'.trans rfl
    rw [hnval]
    exact Nat.ne_of_gt (Nat.add_pos_left hlo _)
  rw [fullStep,
    MobiusExtremaScalar.readExt_srun idx (signalState c idx s) hn,
    hsig, signalState_readExt c idx s]

private theorem signalState_base_frame (c : Cfg) (idx r : Nat)
    (s : RegState) (hg : writes r (signalBlock c) = false) :
    signalState c idx s r = step c idx s r := by
  exact srun_frame idx r (signalBlock c) hg (step c idx s)

private theorem fullStep_base_frame (c : Cfg) (idx r : Nat)
    (s : RegState) (hr : writes r MobiusExtremaScalar.residue = false) :
    fullStep c idx s r = signalState c idx s r := by
  exact srun_frame idx r MobiusExtremaScalar.residue hr (signalState c idx s)

/-- Appending the signal and extrema blocks does not perturb the base trial
observation. -/
theorem fullStep_obs (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hI : Inv s)
    (hidx : idx < c.len * c.rounds) :
    obs (fullStep c idx s) = gstep c idx (obs s) := by
  rw [← body_obs c idx s hadm hI.1 hI.2.1 hI.2.2.1 hI.2.2.2 hidx]
  apply Abs.eq_of
  · exact (fullStep_base_frame c idx 0 s (by rfl)).trans
      (signalState_base_frame c idx 0 s (by rfl))
  · exact (fullStep_base_frame c idx 1 s (by rfl)).trans
      (signalState_base_frame c idx 1 s (by rfl))
  · apply Trial.eq_of
    · exact (fullStep_base_frame c idx 2 s (by rfl)).trans
        (signalState_base_frame c idx 2 s (by rfl))
    · exact (fullStep_base_frame c idx 3 s (by rfl)).trans
        (signalState_base_frame c idx 3 s (by rfl))
    · exact (fullStep_base_frame c idx 4 s (by rfl)).trans
        (signalState_base_frame c idx 4 s (by rfl))

/-- The trial word/bit invariant survives the appended extrema residue. -/
theorem fullStep_inv (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hI : Inv s)
    (hidx : idx < c.len * c.rounds) : Inv (fullStep c idx s) := by
  have hbase := step_inv c idx s hadm hI hidx
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact srun_lt_of_lt idx MobiusExtremaScalar.residue
      (signalState c idx s)
      (srun_lt_of_lt idx (signalBlock c) (step c idx s) hbase.1)
  · rw [fullStep_base_frame c idx 0 s (by rfl),
      signalState_base_frame c idx 0 s (by rfl)]
    exact hbase.2.1
  · rw [fullStep_base_frame c idx 3 s (by rfl),
      signalState_base_frame c idx 3 s (by rfl)]
    exact hbase.2.2.1
  · rw [fullStep_base_frame c idx 4 s (by rfl),
      signalState_base_frame c idx 4 s (by rfl)]
    exact hbase.2.2.2

/-- Joint mathematical state for the trial producer and extrema residue. -/
structure FullAbs where
  base : Abs
  extrema : MobiusExtremaScalar.Ext
  deriving Repr, DecidableEq

theorem FullAbs.eq_of {x y : FullAbs} (hb : x.base = y.base)
    (he : x.extrema = y.extrema) : x = y := by
  cases x
  cases y
  simp_all

def fullObs (s : RegState) : FullAbs :=
  ⟨obs s, MobiusExtremaScalar.readExt s⟩

def fullGstep (c : Cfg) (idx : Nat) (a : FullAbs) : FullAbs :=
  ⟨gstep c idx a.base,
    MobiusExtremaScalar.extStep (roundSig c idx a.base) a.extrema⟩

/-- Joint one-round simulation used by the finite fold bridge. -/
theorem fullStep_fullObs (c : Cfg) (idx : Nat) (s : RegState)
    (hadm : Admissible c) (hlo : 0 < c.lo) (hI : Inv s)
    (hidx : idx < c.len * c.rounds) :
    fullObs (fullStep c idx s) = fullGstep c idx (fullObs s) := by
  apply FullAbs.eq_of
  · exact fullStep_obs c idx s hadm hI hidx
  · exact fullStep_readExt c idx s hadm hlo hI hidx

/-! ## Finite, shardable checker -/

/-- Seed the three persistent fields and clear the aggregate failure count. -/
def extremaInit (e : MobiusExtremaScalar.Ext) : List Instr :=
  [ .mov ArraySegSieve.rT (.lit e.t)
  , .mov ArraySegSieve.rTmax (.lit e.hi)
  , .mov ArraySegSieve.rTmin (.lit e.lo)
  , .mov ArraySegSieve.outputReg (.lit 0) ]

/-- Compare the final extrema with the symmetric fixed-point threshold. -/
def extremaEpilogue (threshold : Nat) : List Instr :=
  [ .binop 91 .gt (.reg ArraySegSieve.rTmax)
      (.lit (ArraySegSieve.tBias + threshold))
  , .binop ArraySegSieve.outputReg .add
      (.reg ArraySegSieve.outputReg) (.reg 91)
  , .binop 91 .lt (.reg ArraySegSieve.rTmin)
      (.lit (ArraySegSieve.tBias - threshold))
  , .binop ArraySegSieve.outputReg .add
      (.reg ArraySegSieve.outputReg) (.reg 91) ]

def fullEntry (c : Cfg) (e : MobiusExtremaScalar.Ext) : RegState :=
  srun 0 (entry c) (extremaInit e)

/-- Executable scalar checker.  A zero output means both final extrema stayed
inside the supplied symmetric threshold. -/
def fullProgram (c : Cfg) (threshold : Nat)
    (e : MobiusExtremaScalar.Ext) : Program :=
  { regCount := 178
  , loopCount := c.len * c.rounds
  , init := initBlock c ++ extremaInit e
  , body := fullBody c
  , epilogue := extremaEpilogue threshold
  , output := ArraySegSieve.outputReg }

/-- Observation variant of the same compiled trace returning the final
accumulator word.  It is used to certify carry handoffs between independently
compiled shards without trusting a generated seed literal. -/
def tProgram (c : Cfg) (e : MobiusExtremaScalar.Ext) : Program :=
  { regCount := 178
  , loopCount := c.len * c.rounds
  , init := initBlock c ++ extremaInit e
  , body := fullBody c
  , epilogue := []
  , output := ArraySegSieve.rT }

theorem fullEntry_init (c : Cfg) (e : MobiusExtremaScalar.Ext) :
    denoteInstrs 0 initialState (initBlock c ++ extremaInit e) =
      some (fullEntry c e) := by
  apply denoteInstrs_append_intro 0 initialState (entry c) (fullEntry c e)
      (initBlock c) (extremaInit e) (entry_init c)
  apply srun_correct
  intro i hi
  simp only [extremaInit, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  all_goals rfl

theorem fullEntry_inv (c : Cfg) (e : MobiusExtremaScalar.Ext) :
    Inv (fullEntry c e) := by
  have he := entry_inv c
  refine ⟨srun_lt_of_lt 0 (extremaInit e) (entry c) he.1, ?_, ?_, ?_⟩
  · rw [fullEntry, srun_frame 0 0 (extremaInit e) (by rfl)]
    exact he.2.1
  · rw [fullEntry, srun_frame 0 3 (extremaInit e) (by rfl)]
    exact he.2.2.1
  · rw [fullEntry, srun_frame 0 4 (extremaInit e) (by rfl)]
    exact he.2.2.2

theorem fullEntry_fullObs (c : Cfg) (e : MobiusExtremaScalar.Ext)
    (hw : MobiusExtremaScalar.ExtWord e) :
    fullObs (fullEntry c e) = ⟨obs (entry c), e⟩ := by
  apply FullAbs.eq_of
  · apply Abs.eq_of
    · simp [fullObs, fullEntry, extremaInit, obs, srun, sdest, sval,
        denoteOperand, RegState.set, ArraySegSieve.rT,
        ArraySegSieve.rTmax, ArraySegSieve.rTmin,
        ArraySegSieve.outputReg]
    · simp [fullObs, fullEntry, extremaInit, obs, srun, sdest, sval,
        denoteOperand, RegState.set, ArraySegSieve.rT,
        ArraySegSieve.rTmax, ArraySegSieve.rTmin,
        ArraySegSieve.outputReg]
    · apply Trial.eq_of <;>
        simp [fullObs, fullEntry, extremaInit, obs, srun, sdest, sval,
          denoteOperand, RegState.set, ArraySegSieve.rT,
          ArraySegSieve.rTmax, ArraySegSieve.rTmin,
          ArraySegSieve.outputReg]
  · rcases hw with ⟨ht, hhi, hlo⟩
    apply MobiusExtremaScalar.Ext.eq_of <;>
      simp [fullObs, fullEntry, extremaInit, MobiusExtremaScalar.readExt,
        srun, sdest, sval, denoteOperand, RegState.set,
        ArraySegSieve.rT, ArraySegSieve.rTmax, ArraySegSieve.rTmin,
        ArraySegSieve.outputReg, Nat.mod_eq_of_lt ht,
        Nat.mod_eq_of_lt hhi, Nat.mod_eq_of_lt hlo]

/-- A bounded list of rounds has a successful concrete trace equal to the
pure `fullStep` fold. -/
theorem fold_denote (c : Cfg) (hlo : 0 < c.lo) (hadm : Admissible c) :
    ∀ (indices : List Nat) (s : RegState),
      (∀ idx ∈ indices, idx < c.len * c.rounds) → Inv s →
      indices.foldlM (fun s idx => denoteInstrs idx s (fullBody c)) s =
        some (indices.foldl (fun s idx => fullStep c idx s) s) := by
  intro indices
  induction indices with
  | nil => intro s _ _; rfl
  | cons idx rest ih =>
      intro s hmem hI
      have hidx : idx < c.len * c.rounds := hmem idx (by simp)
      show (denoteInstrs idx s (fullBody c)).bind
          (fun s => rest.foldlM
            (fun s idx => denoteInstrs idx s (fullBody c)) s) = _
      rw [fullBody_denote c idx s hadm hlo hI hidx]
      exact ih (fullStep c idx s)
        (fun i hi => hmem i (by simp [hi]))
        (fullStep_inv c idx s hadm hI hidx)

/-- Joint observation commutes with every bounded finite trace. -/
theorem fold_fullObs (c : Cfg) (hlo : 0 < c.lo) (hadm : Admissible c) :
    ∀ (indices : List Nat) (s : RegState),
      (∀ idx ∈ indices, idx < c.len * c.rounds) → Inv s →
      fullObs (indices.foldl (fun s idx => fullStep c idx s) s) =
        indices.foldl (fun a idx => fullGstep c idx a) (fullObs s) := by
  intro indices
  induction indices with
  | nil => intro s _ _; rfl
  | cons idx rest ih =>
      intro s hmem hI
      have hidx : idx < c.len * c.rounds := hmem idx (by simp)
      rw [List.foldl_cons,
        ih (fullStep c idx s) (fun i hi => hmem i (by simp [hi]))
          (fullStep_inv c idx s hadm hI hidx),
        fullStep_fullObs c idx s hadm hlo hI hidx]
      rfl

def finalAbs (c : Cfg) (e : MobiusExtremaScalar.Ext) : FullAbs :=
  (List.range (c.len * c.rounds)).foldl
    (fun a idx => fullGstep c idx a) ⟨obs (entry c), e⟩

/-- Exact two-sided failure count computed by the scalar epilogue. -/
def failures (threshold : Nat) (e : MobiusExtremaScalar.Ext) : Nat :=
  (if e.hi > (ArraySegSieve.tBias + threshold) % M then 1 else 0) +
    (if e.lo < (ArraySegSieve.tBias - threshold) % M then 1 else 0)

theorem extremaEpilogue_denote (threshold : Nat) (s : RegState) :
    denoteInstrs 0 s (extremaEpilogue threshold) =
      some (srun 0 s (extremaEpilogue threshold)) := by
  apply srun_correct
  intro i hi
  simp only [extremaEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  all_goals rfl

theorem extremaEpilogue_output (threshold : Nat) (s : RegState)
    (hz : s ArraySegSieve.outputReg = 0) :
    srun 0 s (extremaEpilogue threshold) ArraySegSieve.outputReg =
      failures threshold (MobiusExtremaScalar.readExt s) := by
  simp [ArraySegSieve.outputReg] at hz
  simp [extremaEpilogue, failures, MobiusExtremaScalar.readExt, srun,
    sdest, sval, denoteOperand, denoteOp, RegState.set, hz,
    ArraySegSieve.outputReg, ArraySegSieve.rTmax, ArraySegSieve.rTmin]
  split <;> split <;> decide

private theorem fullStep_output_frame (c : Cfg) (idx : Nat)
    (s : RegState) :
    fullStep c idx s ArraySegSieve.outputReg =
      s ArraySegSieve.outputReg := by
  rw [fullStep, srun_frame idx ArraySegSieve.outputReg
      MobiusExtremaScalar.residue (by rfl)]
  unfold signalState MobiusResidueTrial.signalState
  rw [srun_frame idx ArraySegSieve.outputReg (signalBlock c) (by rfl), step,
    srun_frame idx ArraySegSieve.outputReg (body c) (by rfl)]

theorem fold_output_zero (c : Cfg) : ∀ (indices : List Nat) (s : RegState),
    s ArraySegSieve.outputReg = 0 →
    (indices.foldl (fun s idx => fullStep c idx s) s)
      ArraySegSieve.outputReg = 0 := by
  intro indices
  induction indices with
  | nil => exact fun s h => h
  | cons idx rest ih =>
      intro s hz
      simp only [List.foldl_cons]
      apply ih
      rw [fullStep_output_frame c idx s, hz]

/-- Whole-program denotation of the finite extrema checker. -/
theorem fullProgram_denote (c : Cfg) (threshold : Nat)
    (e : MobiusExtremaScalar.Ext) (hadm : Admissible c) (hlo : 0 < c.lo)
    (hw : MobiusExtremaScalar.ExtWord e) :
    (fullProgram c threshold e).denote =
      some (failures threshold (finalAbs c e).extrema) := by
  let indices := List.range (c.len * c.rounds)
  have hmem : ∀ i ∈ indices, i < c.len * c.rounds :=
    fun i hi => List.mem_range.mp hi
  have hrun := fold_denote c hlo hadm indices (fullEntry c e)
    hmem (fullEntry_inv c e)
  have hobs := fold_fullObs c hlo hadm indices (fullEntry c e)
    hmem (fullEntry_inv c e)
  have hentry := fullEntry_fullObs c e hw
  have hz0 : fullEntry c e ArraySegSieve.outputReg = 0 := by
    simp [fullEntry, extremaInit, srun, sdest, sval, denoteOperand,
      RegState.set, ArraySegSieve.outputReg, ArraySegSieve.rT,
      ArraySegSieve.rTmax, ArraySegSieve.rTmin]
  have hz := fold_output_zero c indices (fullEntry c e) hz0
  have hep := extremaEpilogue_denote threshold
    (indices.foldl (fun s idx => fullStep c idx s) (fullEntry c e))
  unfold Program.denote fullProgram
  simp only
  rw [fullEntry_init c e]
  change (List.foldlM (fun s idx => denoteInstrs idx s (fullBody c))
      (fullEntry c e) indices).bind
      (fun s => (denoteInstrs 0 s (extremaEpilogue threshold)).bind
        (fun s => some (s ArraySegSieve.outputReg))) = _
  rw [hrun]
  simp only [Option.bind_some]
  rw [hep]
  simp only [Option.bind_some]
  rw [extremaEpilogue_output threshold _ hz]
  change some (failures threshold
    (fullObs (indices.foldl (fun s idx => fullStep c idx s)
      (fullEntry c e))).extrema) = _
  rw [hobs, hentry]
  rfl

/-- Whole-program denotation of the final-accumulator observation variant. -/
theorem tProgram_denote (c : Cfg) (e : MobiusExtremaScalar.Ext)
    (hadm : Admissible c) (hlo : 0 < c.lo)
    (hw : MobiusExtremaScalar.ExtWord e) :
    (tProgram c e).denote = some (finalAbs c e).extrema.t := by
  let indices := List.range (c.len * c.rounds)
  have hmem : ∀ i ∈ indices, i < c.len * c.rounds :=
    fun i hi => List.mem_range.mp hi
  have hrun := fold_denote c hlo hadm indices (fullEntry c e)
    hmem (fullEntry_inv c e)
  have hobs := fold_fullObs c hlo hadm indices (fullEntry c e)
    hmem (fullEntry_inv c e)
  have hentry := fullEntry_fullObs c e hw
  unfold Program.denote tProgram
  simp only
  rw [fullEntry_init c e]
  change (List.foldlM (fun s idx => denoteInstrs idx s (fullBody c))
      (fullEntry c e) indices).bind
      (fun s => (denoteInstrs 0 s []).bind
        (fun s => some (s ArraySegSieve.rT))) = _
  rw [hrun]
  simp only [denoteInstrs, Option.bind_some]
  change some (fullObs
    (indices.foldl (fun s idx => fullStep c idx s) (fullEntry c e))).extrema.t = _
  rw [hobs, hentry]
  rfl

end LeanCompCert.Ports.MobiusExtremaTrial

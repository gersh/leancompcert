import LeanCompCert.Ports.R2RuntimePrimePredicate
import LeanCompCert.Ports.R2RuntimePackDenote

/-!
# Mathematical entries written by the compiled R2 table packer

The production table is constructed by CompCert-compiled code.  The lemmas
here reason about an arbitrary finishing round; they never reduce the
3,477,912-step production fold in Lean.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert.Verified.LogFixed
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock

/-- Number of selected candidates among `2, ..., q + 1`.  This is used only
symbolically in proofs; the production value is supplied by the compiled
receipt rather than normalized by Lean. -/
def rootPackCount (arr : Nat → Nat) : Nat → Nat
  | 0 => 0
  | q + 1 => rootPackCount arr q + if arr (q + 2) = 0 then 1 else 0

@[simp] theorem rootPackCount_zero (arr : Nat → Nat) :
    rootPackCount arr 0 = 0 := rfl

@[simp] theorem rootPackCount_succ (arr : Nat → Nat) (q : Nat) :
    rootPackCount arr (q + 1) =
      rootPackCount arr q + if arr (q + 2) = 0 then 1 else 0 := rfl

theorem rootPackCount_le (arr : Nat → Nat) (q : Nat) :
    rootPackCount arr q ≤ q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [rootPackCount_succ]
      split <;> omega

theorem rootPackCount_mono (arr : Nat → Nat) {a b : Nat} (hab : a ≤ b) :
    rootPackCount arr a ≤ rootPackCount arr b := by
  induction hab with
  | refl => exact Nat.le_refl _
  | @step b _ ih =>
      rw [rootPackCount_succ]
      exact Nat.le_add_right_of_le ih

theorem rootPackCount_selected_lt (arr : Nat → Nat) {a b : Nat}
    (hab : a < b) (ha : arr (a + 2) = 0) :
    rootPackCount arr a < rootPackCount arr b := by
  have hstep : rootPackCount arr (a + 1) = rootPackCount arr a + 1 := by
    simp [ha]
  calc
    rootPackCount arr a < rootPackCount arr (a + 1) := by omega
    _ ≤ rootPackCount arr b :=
      rootPackCount_mono arr (by omega : a + 1 ≤ b)

/-- Mathematical rank of the candidates not carrying a bounded composite
witness.  It is a specification only; the production rank is computed by
the compiled marker and packer. -/
noncomputable def rootTrialPrimeCount : Nat → Nat
  | 0 => 0
  | q + 1 => rootTrialPrimeCount q +
      if RootTrialComposite (q + 2) then 0 else 1

@[simp] theorem rootTrialPrimeCount_zero : rootTrialPrimeCount 0 = 0 := rfl

@[simp] theorem rootTrialPrimeCount_succ (q : Nat) :
    rootTrialPrimeCount (q + 1) = rootTrialPrimeCount q +
      if RootTrialComposite (q + 2) then 0 else 1 := rfl

/-- Inside the production root range, the mathematical table rank increments
exactly at primes.  This reformulates the bounded-divisor counter in the
source-facing prime language without evaluating any prefix. -/
theorem rootTrialPrimeCount_succ_prime (q : Nat)
    (hq : q < runtimeRoot - 1) :
    rootTrialPrimeCount (q + 1) = rootTrialPrimeCount q +
      if LeanCompCert.Verified.PackedSieve.IsPrime (q + 2) then 1 else 0 := by
  classical
  rw [rootTrialPrimeCount_succ]
  have hx2 : 2 ≤ q + 2 := by omega
  have hxRoot : q + 2 ≤ runtimeRoot := by omega
  have hcomp := rootTrialComposite_iff_not_prime hx2 hxRoot
  by_cases hp : LeanCompCert.Verified.PackedSieve.IsPrime (q + 2)
  · have hc : ¬ RootTrialComposite (q + 2) :=
      fun h => hcomp.mp h hp
    simp [hp, hc]
  · have hc : RootTrialComposite (q + 2) := by
      apply Classical.byContradiction
      intro hncomp
      have hprime : LeanCompCert.Verified.PackedSieve.IsPrime (q + 2) :=
        Classical.not_not.mp (fun hnprime => hncomp (hcomp.mpr hnprime))
      exact hp hprime
    simp [hp, hc]

/-- Every rank below a finite prime-count prefix is occupied by a unique
candidate that is prime.  The existence form is the part needed by the
production cursor invariant; it is proved by symbolic induction on an
arbitrary prefix and does not construct the production table. -/
theorem exists_prime_of_lt_rootTrialPrimeCount (limit i : Nat)
    (hlimit : limit ≤ runtimeRoot - 1)
    (hi : i < rootTrialPrimeCount limit) :
    ∃ q, q < limit ∧
      LeanCompCert.Verified.PackedSieve.IsPrime (q + 2) ∧
      rootTrialPrimeCount q = i := by
  induction limit with
  | zero => simp at hi
  | succ q ih =>
      have hqRoot : q < runtimeRoot - 1 := by omega
      rw [rootTrialPrimeCount_succ_prime q hqRoot] at hi
      by_cases hp : LeanCompCert.Verified.PackedSieve.IsPrime (q + 2)
      · simp only [hp, if_pos] at hi
        by_cases hbelow : i < rootTrialPrimeCount q
        · obtain ⟨p, hpq, hpPrime, hpRank⟩ := ih (by omega) hbelow
          exact ⟨p, by omega, hpPrime, hpRank⟩
        · have hrank : rootTrialPrimeCount q = i := by omega
          exact ⟨q, by omega, hp, hrank⟩
      · simp only [hp] at hi
        obtain ⟨p, hpq, hpPrime, hpRank⟩ := ih (by omega) hi
        exact ⟨p, by omega, hpPrime, hpRank⟩
/-- The compiled root-marker cells induce exactly the mathematical bounded
trial-prime rank, proved symbolically for any prefix. -/
theorem rootPackCount_marked_eq_trial (q : Nat) (hq : q ≤ runtimeRoot - 1) :
    rootPackCount
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr q =
      rootTrialPrimeCount q := by
  classical
  induction q with
  | zero => rfl
  | succ q ih =>
      have hqPre : q ≤ runtimeRoot - 1 := by omega
      have hx2 : 2 ≤ q + 2 := by omega
      have hxRoot : q + 2 ≤ runtimeRoot := by omega
      have hzero := rootMarkedState_cell_eq_zero_iff (q + 2) hx2 hxRoot
      rw [rootPackCount_succ, rootTrialPrimeCount_succ, ih hqPre]
      by_cases hc : RootTrialComposite (q + 2)
      · have hnzero :
            ¬ (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr
              (q + 2) = 0 := by
          exact fun hz => (hzero.mp hz) hc
        simp [hc, hnzero]
      · have hcell :
            (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr
              (q + 2) = 0 := hzero.mpr hc
        simp [hc, hcell]

/-- Exact mathematical content accumulated before the round at `index`.
The table clause states every selected entry by its rank, rather than asking
Lean to materialize the production list. -/
structure RootPackTableInvariant (arr : Nat → Nat) (index : Nat)
    (m : RootPackModel) : Prop where
  writeEq : m.write = rootPackCount arr (rootPackN index - 2)
  processedZero : ∀ x, 2 ≤ x → x < rootPackN index → m.arr x = 0
  futureEq : ∀ x, rootPackN index ≤ x → x ≤ runtimeRoot →
    m.arr x = arr x
  tableEq : ∀ q, q < rootPackN index - 2 → arr (q + 2) = 0 →
    m.arr (runtimeProductionCfg.tableBase + rootPackCount arr q) =
      packEntry (q + 2)
        (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2)) 1

theorem rootPackObserve_arr (s :
    LeanCompCert.Verified.ArrayState.AState) :
    (rootPackObserve s).arr = s.arr := rfl

theorem rootPackObserve_write (s :
    LeanCompCert.Verified.ArrayState.AState) :
    (rootPackObserve s).write = s.regs rpWrite := rfl

theorem rootPackInitialModel_tableInvariant (arr : Nat → Nat) :
    RootPackTableInvariant arr 0 (rootPackInitialModel arr) := by
  refine
    { writeEq := by rfl
      processedZero := ?_
      futureEq := ?_
      tableEq := ?_ }
  · intro x hx hlt
    simp [rootPackN] at hlt
    omega
  · intro x hx hroot
    rfl
  · intro q hq
    simp [rootPackN] at hq

/-- On the last round for a candidate, the packer's fractional accumulator is
exactly the `runtimeScale`-round source `logFrac`. -/
theorem rootPackAaNext_finish_eq_logFrac (index : Nat) (m : RootPackModel)
    (hinv : RootPackInvariant index m)
    (hfinish : rootPackRound index + 1 = runtimeScale) :
    rootPackAaNext index m =
      logFrac runtimeScale (rootPackNorm index) := by
  simp only [rootPackAaNext, hinv.logState.1, hinv.logState.2,
    logFrac, hfinish.symm, logIter, logStep, Nat.shiftLeft_eq,
    Nat.pow_one, Nat.mul_comm]

/-- Consequently, the packed weight is the same `lnFix` used by the
mathematical R2 specification. -/
theorem rootPackLnValue_finish_eq_lnFix (index : Nat) (m : RootPackModel)
    (hinv : RootPackInvariant index m)
    (hfinish : rootPackRound index + 1 = runtimeScale) :
    rootPackLnValue (rootPackExNext index m) (rootPackAaNext index m) =
      LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale
        (rootPackN index) := by
  rw [hinv.nextEx, rootPackAaNext_finish_eq_logFrac index m hinv hfinish]
  rfl

/-- A selected candidate's finishing round writes its exact mathematical
table entry at the current table cursor and advances that cursor once. -/
theorem rootPackModelStep_finish_selected (c : R2Cfg) (index : Nat)
    (m : RootPackModel)
    (hinv : RootPackInvariant index m)
    (hi : index < (r2RootPackProgram c).loopCount)
    (hbase : runtimeRoot < c.tableBase)
    (hfinish : rootPackRound index + 1 = runtimeScale)
    (hselected : m.arr (rootPackN index) = 0) :
    let out := rootPackModelStep c index m
    out.write = m.write + 1 ∧
      out.arr (m.write + c.tableBase) =
        packEntry (rootPackN index)
          (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale
            (rootPackN index)) 1 := by
  have hnRoot : rootPackN index ≤ runtimeRoot :=
    (rootPack_index_bounds (by
      simpa [r2RootPackProgram] using hi)).2.1
  have haddr : m.write + c.tableBase ≠ rootPackN index := by omega
  have hweight := rootPackLnValue_finish_eq_lnFix index m hinv hfinish
  simp [rootPackModelStep, rootPackHit, rootPackFinish, hfinish,
    rootPackPrime, hselected, rootPackClearTargetSpec,
    rootPackStoreTargetSpec, haddr, hweight]

/-- One symbolic packer round preserves the exact ranked-table invariant.
This is the induction step used for the entire production fold. -/
theorem rootPackTableInvariant_step (arr : Nat → Nat) (index : Nat)
    (m : RootPackModel)
    (hi : index <
      (r2RootPackProgram runtimeProductionCfg).loopCount)
    (hnumeric : RootPackInvariant index m)
    (htable : RootPackTableInvariant arr index m) :
    RootPackTableInvariant arr (index + 1)
      (rootPackModelStep runtimeProductionCfg index m) := by
  have hbounds := rootPack_index_bounds (by
    simpa [r2RootPackProgram] using hi)
  have hnRoot : rootPackN index ≤ runtimeRoot := hbounds.2.1
  have hnTwo : 2 ≤ rootPackN index := by simp [rootPackN]
  have hbase : runtimeRoot < runtimeProductionCfg.tableBase := by decide
  have hsinkRoot : runtimeRoot < runtimeProductionCfg.streamSink := by decide
  have hsinkTable : runtimeProductionCfg.tableBase + runtimeRoot <
      runtimeProductionCfg.streamSink := by decide
  have hround : rootPackRound index + 1 ≤ runtimeScale := by
    have := hbounds.2.2
    omega
  by_cases hf : rootPackRound index + 1 = runtimeScale
  · have hnext := rootPack_succ_at_finish hf
    have hfinishOne : rootPackFinish index = 1 := by
      simp [rootPackFinish, hf]
    have hcur : m.arr (rootPackN index) = arr (rootPackN index) :=
      htable.futureEq _ (Nat.le_refl _) hnRoot
    have hcountIndex :
        rootPackN (index + 1) - 2 = (rootPackN index - 2) + 1 := by
      omega
    by_cases hs : arr (rootPackN index) = 0
    · have hmSelected : m.arr (rootPackN index) = 0 := hcur.trans hs
      have hwrite := (rootPackModelStep_finish_selected
        runtimeProductionCfg index m hnumeric hi hbase hf hmSelected)
      refine
        { writeEq := ?_
          processedZero := ?_
          futureEq := ?_
          tableEq := ?_ }
      · rw [hwrite.1, htable.writeEq, hcountIndex,
          rootPackCount_succ]
        have hnRecover : rootPackN index - 2 + 2 = rootPackN index := by
          omega
        simp [hnRecover, hs]
      · intro x hx hlt
        have hxStore : x ≠ m.write + runtimeProductionCfg.tableBase := by
          omega
        by_cases hxn : x = rootPackN index
        · subst x
          simp [rootPackModelStep, rootPackClearTargetSpec, hf,
            rootPackHit, rootPackFinish, rootPackPrime, hmSelected,
            rootPackStoreTargetSpec]
        · have hprev : m.arr x = 0 :=
            htable.processedZero x hx (by omega)
          simp [rootPackModelStep, rootPackClearTargetSpec, hf,
            rootPackHit, rootPackFinish, rootPackPrime, hmSelected,
            rootPackStoreTargetSpec, hxn, hxStore, hprev]
      · intro x hx hroot
        have hxn : x ≠ rootPackN index := by omega
        have hxStore : x ≠ m.write + runtimeProductionCfg.tableBase := by
          omega
        have hprev := htable.futureEq x (by omega) hroot
        simp [rootPackModelStep, rootPackClearTargetSpec, hf,
          rootPackHit, rootPackFinish, rootPackPrime, hmSelected,
          rootPackStoreTargetSpec, hxn, hxStore, hprev]
      · intro q hq hqSelected
        have hqLe : q ≤ rootPackN index - 2 := by omega
        rcases Nat.lt_or_eq_of_le hqLe with hqOld | hqNow
        · have hold := htable.tableEq q hqOld hqSelected
          have hqRoot : q ≤ runtimeRoot := by omega
          have haddrClear :
              runtimeProductionCfg.tableBase + rootPackCount arr q ≠
                rootPackN index := by omega
          have haddrStore :
              runtimeProductionCfg.tableBase + rootPackCount arr q ≠
                m.write + runtimeProductionCfg.tableBase := by
            rw [htable.writeEq]
            have := rootPackCount_selected_lt arr hqOld hqSelected
            omega
          simp [rootPackModelStep, rootPackClearTargetSpec, hf,
            rootPackHit, rootPackFinish, rootPackPrime, hmSelected,
            rootPackStoreTargetSpec, haddrClear, haddrStore, hold]
        · subst q
          have hnRecover : rootPackN index - 2 + 2 = rootPackN index := by
            omega
          simpa [htable.writeEq, hnRecover, Nat.add_comm] using hwrite.2
    · have hmNotSelected : m.arr (rootPackN index) ≠ 0 := by
        rw [hcur]
        exact hs
      refine
        { writeEq := ?_
          processedZero := ?_
          futureEq := ?_
          tableEq := ?_ }
      · rw [rootPackModelStep, htable.writeEq, hcountIndex,
          rootPackCount_succ]
        have hnRecover : rootPackN index - 2 + 2 = rootPackN index := by
          omega
        simp [rootPackHit, rootPackFinish, hf, rootPackPrime,
          hmNotSelected, hnRecover, hs]
      · intro x hx hlt
        have hxsink : x ≠ runtimeProductionCfg.streamSink := by omega
        by_cases hxn : x = rootPackN index
        · subst x
          simp [rootPackModelStep, rootPackClearTargetSpec, hf,
            rootPackHit, rootPackFinish, rootPackPrime, hmNotSelected,
            rootPackStoreTargetSpec]
        · have hprev : m.arr x = 0 :=
            htable.processedZero x hx (by omega)
          simp [rootPackModelStep, rootPackClearTargetSpec, hf,
            rootPackHit, rootPackFinish, rootPackPrime, hmNotSelected,
            rootPackStoreTargetSpec, hxn, hxsink, hprev]
      · intro x hx hroot
        have hxn : x ≠ rootPackN index := by omega
        have hxsink : x ≠ runtimeProductionCfg.streamSink := by omega
        have hprev := htable.futureEq x (by omega) hroot
        simp [rootPackModelStep, rootPackClearTargetSpec, hf,
          rootPackHit, rootPackFinish, rootPackPrime, hmNotSelected,
          rootPackStoreTargetSpec, hxn, hxsink, hprev]
      · intro q hq hqSelected
        have hqOld : q < rootPackN index - 2 := by
          have hqLe : q ≤ rootPackN index - 2 := by omega
          have hqNe : q ≠ rootPackN index - 2 := by
            intro hqEq
            subst q
            have hnRecover : rootPackN index - 2 + 2 = rootPackN index := by
              omega
            exact hs (by simpa [hnRecover] using hqSelected)
          omega
        have hold := htable.tableEq q hqOld hqSelected
        have haddrClear :
            runtimeProductionCfg.tableBase + rootPackCount arr q ≠
              rootPackN index := by omega
        have haddrSink :
            runtimeProductionCfg.tableBase + rootPackCount arr q ≠
              runtimeProductionCfg.streamSink := by
          have hc := rootPackCount_le arr q
          omega
        have hclear : rootPackClearTargetSpec runtimeProductionCfg index =
            rootPackN index := by
          simp [rootPackClearTargetSpec, hfinishOne]
        have hstore : rootPackStoreTargetSpec runtimeProductionCfg index m =
            runtimeProductionCfg.streamSink := by
          simp [rootPackStoreTargetSpec, rootPackHit, rootPackFinish, hf,
            rootPackPrime, hmNotSelected]
        simp [rootPackModelStep, hclear, hstore, haddrClear, haddrSink, hold]
  · have hbefore : rootPackRound index + 1 < runtimeScale := by omega
    have hnext := rootPack_succ_before_finish hbefore
    have hfinishZero : rootPackFinish index = 0 := by
      simp [rootPackFinish, hf]
    refine
      { writeEq := ?_
        processedZero := ?_
        futureEq := ?_
        tableEq := ?_ }
    · simpa [rootPackModelStep, rootPackHit, hfinishZero, hnext.1]
        using htable.writeEq
    · intro x hx hlt
      have hxsink : x ≠ runtimeProductionCfg.streamSink := by omega
      have hprev := htable.processedZero x hx (by simpa [hnext.1] using hlt)
      simp [rootPackModelStep, rootPackClearTargetSpec, hfinishZero,
        rootPackHit, rootPackStoreTargetSpec, hxsink, hprev]
    · intro x hx hroot
      have hxsink : x ≠ runtimeProductionCfg.streamSink := by omega
      have hprev := htable.futureEq x (by simpa [hnext.1] using hx) hroot
      simp [rootPackModelStep, rootPackClearTargetSpec, hfinishZero,
        rootPackHit, rootPackStoreTargetSpec, hxsink, hprev]
    · intro q hq hqSelected
      have hqOld : q < rootPackN index - 2 := by simpa [hnext.1] using hq
      have hold := htable.tableEq q hqOld hqSelected
      have haddrSink :
          runtimeProductionCfg.tableBase + rootPackCount arr q ≠
            runtimeProductionCfg.streamSink := by
        have hc := rootPackCount_le arr q
        omega
      simp [rootPackModelStep, rootPackClearTargetSpec, hfinishZero,
        rootPackHit, rootPackStoreTargetSpec, haddrSink, hold]

/-- Exact table semantics for every prefix of the source model fold.  The
induction variable is symbolic, so specializing this theorem to the
production trip count does not execute the fold. -/
theorem rootPackModelFold_tableInvariant (arr : Nat → Nat) (k : Nat)
    (hk : k ≤ (r2RootPackProgram runtimeProductionCfg).loopCount) :
    RootPackTableInvariant arr k
      (rootPackModelFold runtimeProductionCfg (rootPackInitialModel arr) k) := by
  induction k with
  | zero =>
      simpa [rootPackModelFold] using rootPackInitialModel_tableInvariant arr
  | succ k ih =>
      rw [rootPackModelFold_succ]
      apply rootPackTableInvariant_step arr k
      · omega
      · exact rootPackModelFold_invariant runtimeProductionCfg
          (rootPackInitialModel arr) k runtimeProductionCfg_rootPackSafe
          (rootPackInitialModel_invariant arr) (by omega)
      · exact ih (by omega)

theorem rootPackLoopState_tableInvariant (arr : Nat → Nat) :
    RootPackTableInvariant arr
      (r2RootPackProgram runtimeProductionCfg).loopCount
      (rootPackObserve (rootPackLoopState runtimeProductionCfg arr)) := by
  have hsafe := rootPackProductionModelFold_safe arr
  have hobs := rootPackFold_observe runtimeProductionCfg
    (rootPackStartedState arr)
    (r2RootPackProgram runtimeProductionCfg).loopCount
    (fun i hi => by
      rw [rootPackStartedState, rootPackInit_observe]
      exact hsafe i hi)
  have hstart : rootPackObserve (rootPackStartedState arr) =
      rootPackInitialModel arr := by
    exact rootPackInit_observe arr
  have hmodel :
      rootPackModelFold runtimeProductionCfg
          (rootPackObserve (rootPackStartedState arr))
          (r2RootPackProgram runtimeProductionCfg).loopCount =
        rootPackModelFold runtimeProductionCfg (rootPackInitialModel arr)
          (r2RootPackProgram runtimeProductionCfg).loopCount := by
    rw [hstart]
  have hobs' : rootPackObserve
      (rootPackLoopState runtimeProductionCfg arr) =
      rootPackModelFold runtimeProductionCfg (rootPackInitialModel arr)
        (r2RootPackProgram runtimeProductionCfg).loopCount := by
    rw [rootPackLoopState]
    exact hobs.trans hmodel
  rw [hobs']
  exact rootPackModelFold_tableInvariant arr _ (Nat.le_refl _)

theorem rootPackProduction_final_candidate :
    rootPackN (r2RootPackProgram runtimeProductionCfg).loopCount =
      runtimeRoot + 1 := by
  rw [show (r2RootPackProgram runtimeProductionCfg).loopCount =
    (runtimeRoot - 1) * runtimeScale by rfl, rootPackN]
  rw [Nat.mul_div_cancel _ (by decide : 0 < runtimeScale)]
  have : 0 < runtimeRoot := by decide
  omega

/-- Every selected production candidate occurs at its mathematical rank in
the loop output, with its exact packed fixed-log entry. -/
theorem rootPackLoopState_table_entry (arr : Nat → Nat) (q : Nat)
    (hq : q < runtimeRoot - 1) (hselected : arr (q + 2) = 0) :
    (rootPackLoopState runtimeProductionCfg arr).arr
        (runtimeProductionCfg.tableBase + rootPackCount arr q) =
      packEntry (q + 2)
        (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2)) 1 := by
  have h := (rootPackLoopState_tableInvariant arr).tableEq q
  have hq' : q <
      rootPackN (r2RootPackProgram runtimeProductionCfg).loopCount - 2 := by
    rw [rootPackProduction_final_candidate]
    omega
  have hentry := h hq' hselected
  rw [rootPackObserve_arr] at hentry
  exact hentry

theorem rootPackLoopState_write_count (arr : Nat → Nat) :
    (rootPackLoopState runtimeProductionCfg arr).regs rpWrite =
      rootPackCount arr (runtimeRoot - 1) := by
  have h := (rootPackLoopState_tableInvariant arr).writeEq
  have hfinal :
      rootPackN (r2RootPackProgram runtimeProductionCfg).loopCount - 2 =
        runtimeRoot - 1 := by
    rw [rootPackProduction_final_candidate]
    have : 0 < runtimeRoot := by decide
    omega
  calc
    (rootPackLoopState runtimeProductionCfg arr).regs rpWrite =
        (rootPackObserve
          (rootPackLoopState runtimeProductionCfg arr)).write := by
      exact (rootPackObserve_write _).symm
    _ = rootPackCount arr
        (rootPackN (r2RootPackProgram runtimeProductionCfg).loopCount - 2) := h
    _ = rootPackCount arr (runtimeRoot - 1) := congrArg _ hfinal

/-- The sentinel epilogue does not alter the table write cursor. -/
theorem rootPackEpilogue_rpWrite (s :
    LeanCompCert.Verified.ArrayState.AState) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun 0 s
      (rootPackEpilogue runtimeProductionCfg)).regs rpWrite =
        s.regs rpWrite := by
  simp [rootPackEpilogue, arun, astep, sval, sdest, denoteOperand,
    AState.writeReg, AState.writeArr_regs, rpWrite]

/-- Name the definitional handoff from the symbolic loop state to the packed
state.  Keeping the configuration generic prevents elaboration from reducing
the concrete production loop count while later proofs rewrite this seam. -/
theorem rootPackedState_eq_loop_epilogue (c : R2Cfg) (arr : Nat → Nat) :
    rootPackedState c arr =
      arun 0 (rootPackLoopState c arr) (rootPackEpilogue c) := by
  rfl

/-- Exact source result of the production packer.  This strengthens the
older existential execution theorem with the named symbolic output state;
the production fold remains opaque. -/
theorem rootPackProduction_runFromArray_exact (arr : Nat → Nat) :
    (r2RootPackProgram runtimeProductionCfg).runFromArray arr =
      some (rootPackedState runtimeProductionCfg arr) := by
  rw [rootPackedState_eq_loop_epilogue]
  exact rootPackRunFromArray_of_stages runtimeProductionCfg arr
    (rootPackStartedState arr)
    (rootPackLoopState runtimeProductionCfg arr)
    (arun 0 (rootPackLoopState runtimeProductionCfg arr)
      (rootPackEpilogue runtimeProductionCfg))
    (rootPackStartedState_denote runtimeProductionCfg arr)
    (rootPackLoopState_denote runtimeProductionCfg arr
      runtimeProductionCfg_rootPackSafe)
    (rootPackLoopState_epilogue_denote runtimeProductionCfg arr
      runtimeProductionCfg_rootPackSafe)

/-- The exact selected-candidate count survives the packer epilogue. -/
theorem rootPackedState_write_count (arr : Nat → Nat) :
    (rootPackedState runtimeProductionCfg arr).regs rpWrite =
      rootPackCount arr (runtimeRoot - 1) := by
  rw [rootPackedState_eq_loop_epilogue]
  rw [rootPackEpilogue_rpWrite]
  exact rootPackLoopState_write_count arr

/-- The epilogue writes its inert sentinel at the current write cursor. -/
theorem rootPackEpilogue_arr_at_write
    (c : R2Cfg) (s : LeanCompCert.Verified.ArrayState.AState)
    (hword : s.regs rpWrite + c.tableBase < M) :
    (arun 0 s (rootPackEpilogue c)).arr
        (s.regs rpWrite + c.tableBase) =
      packEntry 1 0 0 := by
  have haddrMod : (s.regs rpWrite + c.tableBase) % M =
      s.regs rpWrite + c.tableBase := Nat.mod_eq_of_lt hword
  have hpack : packEntry 1 0 0 < M := by decide
  have hpackMod : packEntry 1 0 0 % M = packEntry 1 0 0 :=
    Nat.mod_eq_of_lt hpack
  simp [rootPackEpilogue, arun, astep, sval, sdest, denoteOperand,
    denoteOp, AState.writeReg, AState.writeArr, haddrMod, hpackMod]

/-- The packer epilogue writes the exact inert sentinel immediately after
the last selected prime.  This is the terminal row used by the main sweep's
clamped cursor. -/
theorem rootPackedState_sentinel (arr : Nat → Nat) :
    (rootPackedState runtimeProductionCfg arr).arr
        (runtimeProductionCfg.tableBase +
          rootPackCount arr (runtimeRoot - 1)) = packEntry 1 0 0 := by
  rw [rootPackedState_eq_loop_epilogue]
  have hcount := rootPackLoopState_write_count arr
  have hwrite :
      (rootPackLoopState runtimeProductionCfg arr).regs rpWrite +
          runtimeProductionCfg.tableBase < M := by
    rw [hcount]
    have hc := rootPackCount_le arr (runtimeRoot - 1)
    have hlayout : runtimeRoot + runtimeProductionCfg.tableBase < M := by decide
    omega
  rw [← hcount]
  rw [Nat.add_comm runtimeProductionCfg.tableBase]
  exact rootPackEpilogue_arr_at_write runtimeProductionCfg
    (rootPackLoopState runtimeProductionCfg arr) hwrite

/-- The sentinel-writing epilogue preserves every other array cell. -/
theorem rootPackEpilogue_arr_of_ne (s : LeanCompCert.Verified.ArrayState.AState)
    (x : Nat)
    (hword : s.regs rpWrite + runtimeProductionCfg.tableBase <
      LeanCompCert.Verified.Reflect.M)
    (hne : x ≠ s.regs rpWrite + runtimeProductionCfg.tableBase) :
    (LeanCompCert.Verified.ArrayFoldBridge.arun 0 s
      (rootPackEpilogue runtimeProductionCfg)).arr x = s.arr x := by
  simp [rootPackEpilogue, arun, astep, sval, sdest, denoteOperand,
    denoteOp, AState.writeReg, AState.writeArr,
    Nat.mod_eq_of_lt hword, hne]

/-- The exact entry theorem survives the sentinel epilogue and therefore
describes the array passed to the compiled main R2 sweep. -/
theorem rootPackedState_table_entry (arr : Nat → Nat) (q : Nat)
    (hq : q < runtimeRoot - 1) (hselected : arr (q + 2) = 0) :
    (rootPackedState runtimeProductionCfg arr).arr
        (runtimeProductionCfg.tableBase + rootPackCount arr q) =
      packEntry (q + 2)
        (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2)) 1 := by
  have hentry := rootPackLoopState_table_entry arr q hq hselected
  have hrankLt : rootPackCount arr q <
      rootPackCount arr (runtimeRoot - 1) :=
    rootPackCount_selected_lt arr hq hselected
  have hne : runtimeProductionCfg.tableBase + rootPackCount arr q ≠
      (rootPackLoopState runtimeProductionCfg arr).regs rpWrite +
        runtimeProductionCfg.tableBase := by
    rw [rootPackLoopState_write_count]
    omega
  have hword :
      (rootPackLoopState runtimeProductionCfg arr).regs rpWrite +
          runtimeProductionCfg.tableBase < M := by
    calc
      (rootPackLoopState runtimeProductionCfg arr).regs rpWrite +
          runtimeProductionCfg.tableBase =
          rootPackCount arr (runtimeRoot - 1) +
            runtimeProductionCfg.tableBase :=
        congrArg (fun z => z + runtimeProductionCfg.tableBase)
          (rootPackLoopState_write_count arr)
      _ < M := by
        have hc := rootPackCount_le arr (runtimeRoot - 1)
        have hlayout : runtimeRoot + runtimeProductionCfg.tableBase < M :=
          by decide
        omega
  have hframe := rootPackEpilogue_arr_of_ne
    (rootPackLoopState runtimeProductionCfg arr)
    (runtimeProductionCfg.tableBase + rootPackCount arr q) hword hne
  have hpacked : rootPackedState runtimeProductionCfg arr =
      arun 0 (rootPackLoopState runtimeProductionCfg arr)
        (rootPackEpilogue runtimeProductionCfg) := by rfl
  exact congrArg
    (fun s => s.arr
      (runtimeProductionCfg.tableBase + rootPackCount arr q)) hpacked |>.trans
      (hframe.trans hentry)

/-- End-to-end mathematical meaning of every table entry produced by the
compiled marker/packer pipeline. -/
theorem rootProductionPackedState_table_entry (q : Nat)
    (hq : q < runtimeRoot - 1)
    (hprime : ¬ RootTrialComposite (q + 2)) :
    (rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr
        (runtimeProductionCfg.tableBase + rootTrialPrimeCount q) =
      packEntry (q + 2)
        (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2)) 1 := by
  have hx2 : 2 ≤ q + 2 := by omega
  have hxRoot : q + 2 ≤ runtimeRoot := by omega
  have hselected :
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr (q + 2) = 0 :=
    (rootMarkedState_cell_eq_zero_iff (q + 2) hx2 hxRoot).mpr hprime
  have hentry := rootPackedState_table_entry
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr q hq hselected
  have hrank := rootPackCount_marked_eq_trial q (Nat.le_of_lt hq)
  have haddr : runtimeProductionCfg.tableBase + rootTrialPrimeCount q =
      runtimeProductionCfg.tableBase + rootPackCount
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr q := by
    exact congrArg (fun z => runtimeProductionCfg.tableBase + z) hrank.symm
  exact congrArg
    (fun x => (rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr x)
    haddr |>.trans hentry

/-- Source-facing form of the production table theorem: every ordinary prime
in the complete root interval occurs at its exact prime rank with its exact
fixed-log packed entry. -/
theorem rootProductionPackedState_prime_entry (q : Nat)
    (hq : q < runtimeRoot - 1)
    (hprime : LeanCompCert.Verified.PackedSieve.IsPrime (q + 2)) :
    (rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr
        (runtimeProductionCfg.tableBase + rootTrialPrimeCount q) =
      packEntry (q + 2)
        (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2)) 1 := by
  have hx2 : 2 ≤ q + 2 := by omega
  have hxRoot : q + 2 ≤ runtimeRoot := by omega
  apply rootProductionPackedState_table_entry q hq
  intro hcomp
  exact (rootTrialComposite_iff_not_prime hx2 hxRoot).mp hcomp hprime

/-- The compiled production table's terminal cursor is the exact symbolic
number of primes in the root interval. -/
theorem rootProductionPackedState_write_count :
    (rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).regs rpWrite =
        rootTrialPrimeCount (runtimeRoot - 1) := by
  rw [rootPackedState_write_count]
  exact rootPackCount_marked_eq_trial (runtimeRoot - 1) (Nat.le_refl _)

/-- Production specialization of the terminal sentinel theorem. -/
theorem rootProductionPackedState_sentinel :
    (rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr
        (runtimeProductionCfg.tableBase +
          rootTrialPrimeCount (runtimeRoot - 1)) = packEntry 1 0 0 := by
  have h := rootPackedState_sentinel
    (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr
  rw [rootPackCount_marked_eq_trial (runtimeRoot - 1) (Nat.le_refl _)] at h
  exact h

/-- Cursor-facing completeness theorem.  Every resident table index below
the compiled terminal cursor names an actual prime, at its exact rank, and
the corresponding array word is the verified fixed-log packed entry.  The
proof is independent of the production table length and performs no table
construction in Lean. -/
theorem rootProductionPackedState_entry_of_index (i : Nat)
    (hi : i < (rootPackedState runtimeProductionCfg
      (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).regs rpWrite) :
    ∃ q, q < runtimeRoot - 1 ∧
      LeanCompCert.Verified.PackedSieve.IsPrime (q + 2) ∧
      rootTrialPrimeCount q = i ∧
      (rootPackedState runtimeProductionCfg
        (rootMarkedState runtimeProductionCfg (fun _ => 0)).arr).arr
          (runtimeProductionCfg.tableBase + i) =
        packEntry (q + 2)
          (LeanCompCert.Ports.PsiSegSieve.lnFix runtimeScale (q + 2)) 1 := by
  rw [rootProductionPackedState_write_count] at hi
  obtain ⟨q, hq, hprime, hrank⟩ :=
    exists_prime_of_lt_rootTrialPrimeCount (runtimeRoot - 1) i
      (Nat.le_refl _) hi
  refine ⟨q, hq, hprime, hrank, ?_⟩
  rw [← hrank]
  exact rootProductionPackedState_prime_entry q hq hprime

/-! ## Cursor-facing packed-word decoding -/

/-- The low field of a packed runtime table word is its prime value. -/
theorem packEntry_value_decode (v w : Nat) (hv : v < 2 ^ valBits) :
    packEntry v w 1 &&& maskVal = v := by
  rw [maskVal, Nat.and_two_pow_sub_one_eq_mod]
  have hshape : packEntry v w 1 =
      v + 2 ^ valBits * (w + 2 ^ wtBits) := by
    simp only [packEntry, Nat.one_mul, valBits, wtBits]
    omega
  rw [hshape, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv]

/-- Word safety forces the middle field of a production packed word to fit
the declared 28-bit logarithmic-weight lane. -/
theorem packEntry_weight_lt (v w : Nat) (hword : packEntry v w 1 < M) :
    w < 2 ^ wtBits := by
  simp only [packEntry, Nat.one_mul, valBits, wtBits, M] at hword ⊢
  omega

/-- The middle field of a word-safe packed runtime table word is its exact
fixed-log weight. -/
theorem packEntry_weight_decode (v w : Nat) (hv : v < 2 ^ valBits)
    (hword : packEntry v w 1 < M) :
    ((packEntry v w 1 >>> valBits) &&& maskWt) = w := by
  have hw : w < 2 ^ wtBits := packEntry_weight_lt v w hword
  have hshape : packEntry v w 1 =
      v + 2 ^ valBits * (w + 2 ^ wtBits) := by
    simp only [packEntry, Nat.one_mul, valBits, wtBits]
    omega
  rw [hshape, Nat.shiftRight_eq_div_pow,
    Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt hv, Nat.zero_add, maskWt,
    Nat.and_two_pow_sub_one_eq_mod]
  calc
    (w + 2 ^ wtBits) % 2 ^ wtBits = w % 2 ^ wtBits := by
      rw [show 2 ^ wtBits = 2 ^ wtBits * 1 by omega]
      exact Nat.add_mul_mod_self_left w (2 ^ wtBits) 1
    _ = w := Nat.mod_eq_of_lt hw

#print axioms rootPackAaNext_finish_eq_logFrac
#print axioms rootPackLnValue_finish_eq_lnFix
#print axioms rootTrialPrimeCount_succ_prime
#print axioms exists_prime_of_lt_rootTrialPrimeCount
#print axioms rootPackModelStep_finish_selected
#print axioms rootPackModelFold_tableInvariant
#print axioms rootPackedState_table_entry
#print axioms rootPackProduction_runFromArray_exact
#print axioms rootPackedState_write_count
#print axioms rootPackEpilogue_arr_at_write
#print axioms rootPackedState_sentinel
#print axioms rootProductionPackedState_table_entry
#print axioms rootProductionPackedState_prime_entry
#print axioms rootProductionPackedState_write_count
#print axioms rootProductionPackedState_sentinel
#print axioms rootProductionPackedState_entry_of_index
#print axioms packEntry_value_decode
#print axioms packEntry_weight_lt
#print axioms packEntry_weight_decode

end LeanCompCert.Ports.R2SegSieve

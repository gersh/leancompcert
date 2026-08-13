import LeanCompCert.Ports.R2RuntimePackDenote

/-!
# Compiled receipt checker for the production R2 runtime table

The historical benchmark driver computed the table hash and endpoint checks
in handwritten host C.  This module makes those checks an `AProgram`, so the
receipt computation is emitted through the verified compiler too.  Its fixed
13,416-cell fold stays opaque in Lean; all proofs below are symbolic in the
fold length.
-/

namespace LeanCompCert.Ports.R2SegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Ports.ArraySegSieve

def rootReceiptHashInit : Nat := 0
def rootReceiptExpectedHash : Nat := 9835025649024566695
def rootReceiptExpectedFirst : Nat := 9622944148755578882
def rootReceiptExpectedLast : Nat := 16073911806745261571

def rrHash : Nat := 2
def rrAddr : Nat := 3
def rrCell : Nat := 4
def rrFirst : Nat := 5
def rrLast : Nat := 6
def rrSentinel : Nat := 7
def rrFirstOK : Nat := 8
def rrLastOK : Nat := 9
def rrSentinelOK : Nat := 10
def rrHashOK : Nat := 11
def rrFail : Nat := 12
def rootReceiptRegCount : Nat := 13

def rootReceiptInit : List AInstr :=
  [.scalar (.mov rrHash (.lit rootReceiptHashInit))]

def rootReceiptBody (c : R2Cfg) : List AInstr :=
  [ .scalar (.binop rrAddr .add (.lit c.tableBase) .idx)
  , .load rrCell rrAddr
  , .scalar (.binop rrHash .add (.reg rrHash) (.reg rrCell)) ]

def rootReceiptEpilogue (c : R2Cfg) : List AInstr :=
  [ .scalar (.mov rrAddr (.lit c.tableBase))
  , .load rrFirst rrAddr
  , .scalar (.binop rrFail .ne (.reg rrFirst)
      (.lit rootReceiptExpectedFirst))
  , .scalar (.mov rrAddr (.lit (c.tableBase + runtimePrimeCount - 1)))
  , .load rrLast rrAddr
  , .scalar (.binop rrCell .ne (.reg rrLast)
      (.lit rootReceiptExpectedLast))
  , .scalar (.binop rrFail .add (.reg rrFail) (.reg rrCell))
  , .scalar (.mov rrAddr (.lit (c.tableBase + runtimePrimeCount)))
  , .load rrSentinel rrAddr
  , .scalar (.binop rrCell .ne (.reg rrSentinel) (.lit 1))
  , .scalar (.binop rrFail .add (.reg rrFail) (.reg rrCell))
  , .scalar (.binop rrCell .ne (.reg rrHash)
      (.lit rootReceiptExpectedHash))
  , .scalar (.binop rrFail .add (.reg rrFail) (.reg rrCell)) ]

def rootReceiptProgram (c : R2Cfg := runtimeProductionCfg) : AProgram :=
  { regCount := rootReceiptRegCount
    arrayLen := c.arrayLen
    loopCount := runtimePrimeCount + 1
    init := rootReceiptInit
    body := rootReceiptBody c
    epilogue := rootReceiptEpilogue c
    output := rrFail }

/-- Observable checksum program used by the benchmark receipt.  The accepting
checker below recomputes the same fold and compares it to the pinned value. -/
def rootChecksumProgram (c : R2Cfg := runtimeProductionCfg) : AProgram :=
  { regCount := rootReceiptRegCount
    arrayLen := c.arrayLen
    loopCount := runtimePrimeCount + 1
    init := rootReceiptInit
    body := rootReceiptBody c
    epilogue := []
    output := rrHash }

theorem rootReceiptProgram_wf (c : R2Cfg) : (rootReceiptProgram c).WF := by
  unfold rootReceiptProgram
  refine ⟨show rrFail < rootReceiptRegCount by decide, ?_, ?_, ?_⟩
  · exact forall_wf_of_all (by rfl)
  · exact forall_wf_of_all (by rfl)
  · exact forall_wf_of_all (by rfl)

theorem rootChecksumProgram_wf (c : R2Cfg) : (rootChecksumProgram c).WF := by
  unfold rootChecksumProgram
  refine ⟨show rrHash < rootReceiptRegCount by decide, ?_, ?_, ?_⟩
  · exact forall_wf_of_all (by rfl)
  · exact forall_wf_of_all (by rfl)
  · intro a h
    cases h

def rootReceiptHashStep (arr : Nat → Nat) (hash index : Nat) : Nat :=
  (hash + arr (runtimeProductionCfg.tableBase + index)) % M

def rootReceiptHashFold (arr : Nat → Nat) (count : Nat) : Nat :=
  (List.range count).foldl (rootReceiptHashStep arr) rootReceiptHashInit

def RootReceiptOK (arr : Nat → Nat) : Prop :=
  arr runtimeProductionCfg.tableBase = rootReceiptExpectedFirst ∧
  arr (runtimeProductionCfg.tableBase + runtimePrimeCount - 1) =
    rootReceiptExpectedLast ∧
  arr (runtimeProductionCfg.tableBase + runtimePrimeCount) = 1 ∧
  rootReceiptHashFold arr (runtimePrimeCount + 1) =
    rootReceiptExpectedHash

theorem rootReceiptBody_defined (c : R2Cfg) (index : Nat) (s : AState)
    (hi : index < runtimePrimeCount + 1)
    (hArray : c.arrayLen < M)
    (hTable : c.tableBase + runtimePrimeCount < c.arrayLen) :
    AllDefined c.arrayLen index s (rootReceiptBody c) := by
  have hiM : index % M = index := Nat.mod_eq_of_lt (by
    exact Nat.lt_trans hi (by decide))
  have htableM : c.tableBase % M = c.tableBase := Nat.mod_eq_of_lt (by
    omega)
  have haddr : c.tableBase + index < c.arrayLen := by omega
  have haddrM : (c.tableBase + index) % M = c.tableBase + index :=
    Nat.mod_eq_of_lt (Nat.lt_trans haddr hArray)
  simp [rootReceiptBody, AllDefined, ADefined, astep, sval, sdest,
    denoteOperand, denoteOp, AState.writeReg, hiM, htableM, haddrM, haddr]

theorem rootReceiptBody_hash_run (c : R2Cfg) (index : Nat) (s : AState)
    (hi : index < runtimePrimeCount + 1)
    (hArray : c.arrayLen < M)
    (hTable : c.tableBase + runtimePrimeCount < c.arrayLen) :
    (arun index s (rootReceiptBody c)).regs rrHash =
      (s.regs rrHash + s.arr (c.tableBase + index)) % M := by
  have hiM : index % M = index := Nat.mod_eq_of_lt (by
    exact Nat.lt_trans hi (by decide))
  have htableM : c.tableBase % M = c.tableBase := Nat.mod_eq_of_lt (by
    omega)
  have haddr : c.tableBase + index < c.arrayLen := by omega
  have haddrM : (c.tableBase + index) % M = c.tableBase + index :=
    Nat.mod_eq_of_lt (Nat.lt_trans haddr hArray)
  simp [rootReceiptBody, arun, astep, sval, sdest, denoteOperand, denoteOp,
    AState.writeReg, rrHash, rrCell, rrAddr, hiM, htableM, haddrM]

theorem rootReceiptBody_arr_run (c : R2Cfg) (index : Nat) (s : AState) :
    (arun index s (rootReceiptBody c)).arr = s.arr := by
  simp [rootReceiptBody, arun, astep, AState.writeReg]

def rootReceiptStartedState (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr) rootReceiptInit

def rootReceiptMachineFold (arr : Nat → Nat) (count : Nat) : AState :=
  (List.range count).foldl
    (fun s index => arun index s (rootReceiptBody runtimeProductionCfg))
    (rootReceiptStartedState arr)

theorem rootReceiptStartedState_hash (arr : Nat → Nat) :
    (rootReceiptStartedState arr).regs rrHash = rootReceiptHashInit := by
  simp [rootReceiptStartedState, rootReceiptInit, arun, astep, sval, sdest,
    denoteOperand, AState.writeReg, rrHash, rootReceiptHashInit]

theorem rootReceiptStartedState_arr (arr : Nat → Nat) :
    (rootReceiptStartedState arr).arr = arr := by
  simp [rootReceiptStartedState, rootReceiptInit, arun, astep,
    initialAStateWithArray, AState.writeReg]

theorem rootReceiptMachineFold_succ (arr : Nat → Nat) (count : Nat) :
    rootReceiptMachineFold arr (count + 1) =
      arun count (rootReceiptMachineFold arr count)
        (rootReceiptBody runtimeProductionCfg) := by
  simp [rootReceiptMachineFold, List.range_succ, List.foldl_append]

theorem rootReceiptHashFold_succ (arr : Nat → Nat) (count : Nat) :
    rootReceiptHashFold arr (count + 1) =
      rootReceiptHashStep arr (rootReceiptHashFold arr count) count := by
  simp [rootReceiptHashFold, List.range_succ, List.foldl_append]

theorem rootReceiptMachineFold_spec (arr : Nat → Nat) (count : Nat)
    (hcount : count ≤ runtimePrimeCount + 1) :
    (rootReceiptMachineFold arr count).regs rrHash =
        rootReceiptHashFold arr count ∧
      (rootReceiptMachineFold arr count).arr = arr := by
  induction count with
  | zero =>
      exact ⟨rootReceiptStartedState_hash arr,
        rootReceiptStartedState_arr arr⟩
  | succ count ih =>
      have hi : count < runtimePrimeCount + 1 := by omega
      have ih' := ih (by omega)
      rw [rootReceiptMachineFold_succ, rootReceiptHashFold_succ]
      constructor
      · rw [rootReceiptBody_hash_run runtimeProductionCfg count
          (rootReceiptMachineFold arr count) hi (by decide) (by decide),
          ih'.1, ih'.2]
        rfl
      · rw [rootReceiptBody_arr_run, ih'.2]

theorem rootReceiptInit_denote (arr : Nat → Nat) :
    denoteAInstrs runtimeProductionCfg.arrayLen 0
      (initialAStateWithArray arr) rootReceiptInit =
      some (rootReceiptStartedState arr) := by
  apply denoteAInstrs_eq_arun
  simp [rootReceiptInit, AllDefined, ADefined]

theorem rootReceiptDenoteFold (arr : Nat → Nat) (count : Nat)
    (hcount : count ≤ runtimePrimeCount + 1) :
    (List.range count).foldlM
        (fun s index => denoteAInstrs runtimeProductionCfg.arrayLen index s
          (rootReceiptBody runtimeProductionCfg))
        (rootReceiptStartedState arr) =
      some (rootReceiptMachineFold arr count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.range_succ, List.foldlM_append, ih (by omega)]
      have hsome :
          (do
            let init ← (some (rootReceiptMachineFold arr count) : Option AState)
            List.foldlM
              (fun s index => denoteAInstrs runtimeProductionCfg.arrayLen
                index s (rootReceiptBody runtimeProductionCfg)) init [count]) =
          List.foldlM
            (fun s index => denoteAInstrs runtimeProductionCfg.arrayLen
              index s (rootReceiptBody runtimeProductionCfg))
            (rootReceiptMachineFold arr count) [count] :=
        Option.bind_some _ _
      rw [hsome]
      have hdef := rootReceiptBody_defined runtimeProductionCfg count
        (rootReceiptMachineFold arr count) (by omega) (by decide) (by decide)
      have hden := denoteAInstrs_eq_arun runtimeProductionCfg.arrayLen count
        (rootReceiptBody runtimeProductionCfg)
        (rootReceiptMachineFold arr count) hdef
      have htail :
          (do
            let init ← some (arun count (rootReceiptMachineFold arr count)
              (rootReceiptBody runtimeProductionCfg))
            List.foldlM
              (fun s index => denoteAInstrs runtimeProductionCfg.arrayLen
                index s (rootReceiptBody runtimeProductionCfg)) init []) =
          List.foldlM
            (fun s index => denoteAInstrs runtimeProductionCfg.arrayLen
              index s (rootReceiptBody runtimeProductionCfg))
            (arun count (rootReceiptMachineFold arr count)
              (rootReceiptBody runtimeProductionCfg)) [] :=
        Option.bind_some _ _
      rw [List.foldlM_cons, hden, htail, List.foldlM_nil,
        rootReceiptMachineFold_succ]
      rfl

theorem rootReceiptEpilogue_defined (s : AState) :
    AllDefined runtimeProductionCfg.arrayLen 0 s
      (rootReceiptEpilogue runtimeProductionCfg) := by
  have hbase : runtimeProductionCfg.tableBase <
      runtimeProductionCfg.arrayLen := by decide
  have hlast : runtimeProductionCfg.tableBase + runtimePrimeCount - 1 <
      runtimeProductionCfg.arrayLen := by decide
  have hsentinel : runtimeProductionCfg.tableBase + runtimePrimeCount <
      runtimeProductionCfg.arrayLen := by decide
  have hbaseM : runtimeProductionCfg.tableBase % M =
      runtimeProductionCfg.tableBase := by decide
  have hlastM :
      (runtimeProductionCfg.tableBase + runtimePrimeCount - 1) % M =
        runtimeProductionCfg.tableBase + runtimePrimeCount - 1 := by decide
  have hsentinelM :
      (runtimeProductionCfg.tableBase + runtimePrimeCount) % M =
        runtimeProductionCfg.tableBase + runtimePrimeCount := by decide
  simp [rootReceiptEpilogue, AllDefined, ADefined, astep, sval, sdest,
    denoteOperand, denoteOp, AState.writeReg, hbase, hlast, hsentinel,
    hbaseM, hlastM, hsentinelM]

theorem rootReceiptEpilogue_zero (arr : Nat → Nat) (s : AState)
    (harr : s.arr = arr) (hhash : s.regs rrHash = rootReceiptExpectedHash)
    (hok : RootReceiptOK arr) :
    (arun 0 s (rootReceiptEpilogue runtimeProductionCfg)).regs rrFail = 0 := by
  obtain ⟨hfirst, hlast, hsentinel, hsum⟩ := hok
  have hbaseM : runtimeProductionCfg.tableBase % M =
      runtimeProductionCfg.tableBase := by decide
  have hlastM :
      (runtimeProductionCfg.tableBase + runtimePrimeCount - 1) % M =
        runtimeProductionCfg.tableBase + runtimePrimeCount - 1 := by decide
  have hsentinelM :
      (runtimeProductionCfg.tableBase + runtimePrimeCount) % M =
        runtimeProductionCfg.tableBase + runtimePrimeCount := by decide
  have hfirstM : rootReceiptExpectedFirst % M =
      rootReceiptExpectedFirst := by decide
  have hlastExpectedM : rootReceiptExpectedLast % M =
      rootReceiptExpectedLast := by decide
  have hhashM : rootReceiptExpectedHash % M =
      rootReceiptExpectedHash := by decide
  have honeM : 1 % M = 1 := Nat.mod_eq_of_lt (by decide)
  have hhash2 : s.regs 2 = rootReceiptExpectedHash := by
    simpa only [rrHash] using hhash
  simp [rootReceiptEpilogue, arun, astep, sval, sdest, denoteOperand,
    denoteOp, AState.writeReg, harr, hhash2, hfirst, hlast, hsentinel,
    hbaseM, hlastM, hsentinelM, hfirstM, hlastExpectedM, hhashM,
    honeM, rrFail, rrCell, rrAddr, rrFirst, rrLast, rrSentinel, rrHash]

theorem rootReceiptEpilogue_zero_sound (arr : Nat → Nat) (s : AState)
    (harr : s.arr = arr)
    (hzero :
      (arun 0 s (rootReceiptEpilogue runtimeProductionCfg)).regs rrFail = 0) :
    arr runtimeProductionCfg.tableBase = rootReceiptExpectedFirst ∧
      arr (runtimeProductionCfg.tableBase + runtimePrimeCount - 1) =
        rootReceiptExpectedLast ∧
      arr (runtimeProductionCfg.tableBase + runtimePrimeCount) = 1 ∧
      s.regs rrHash = rootReceiptExpectedHash := by
  have hbaseM : runtimeProductionCfg.tableBase % M =
      runtimeProductionCfg.tableBase := by decide
  have hlastM :
      (runtimeProductionCfg.tableBase + runtimePrimeCount - 1) % M =
        runtimeProductionCfg.tableBase + runtimePrimeCount - 1 := by decide
  have hsentinelM :
      (runtimeProductionCfg.tableBase + runtimePrimeCount) % M =
        runtimeProductionCfg.tableBase + runtimePrimeCount := by decide
  have hfirstM : rootReceiptExpectedFirst % M =
      rootReceiptExpectedFirst := by decide
  have hlastExpectedM : rootReceiptExpectedLast % M =
      rootReceiptExpectedLast := by decide
  have hhashM : rootReceiptExpectedHash % M =
      rootReceiptExpectedHash := by decide
  have honeM : 1 % M = 1 := Nat.mod_eq_of_lt (by decide)
  have htwoM : 2 % M = 2 := Nat.mod_eq_of_lt (by decide)
  have hthreeM : 3 % M = 3 := Nat.mod_eq_of_lt (by decide)
  have hfourM : 4 % M = 4 := Nat.mod_eq_of_lt (by decide)
  by_cases hfirst :
      arr runtimeProductionCfg.tableBase = rootReceiptExpectedFirst <;>
    by_cases hlast :
      arr (runtimeProductionCfg.tableBase + runtimePrimeCount - 1) =
        rootReceiptExpectedLast <;>
    by_cases hsentinel :
      arr (runtimeProductionCfg.tableBase + runtimePrimeCount) = 1 <;>
    by_cases hhash : s.regs 2 = rootReceiptExpectedHash
  all_goals
    simp [rootReceiptEpilogue, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, harr, hfirst, hlast, hsentinel, hhash,
      hbaseM, hlastM, hsentinelM, hfirstM, hlastExpectedM, hhashM,
      honeM, htwoM, hthreeM, hfourM, rrFail, rrCell, rrAddr, rrFirst,
      rrLast, rrSentinel,
      rrHash] at hzero
  exact ⟨hfirst, hlast, hsentinel, by simpa only [rrHash] using hhash⟩

def rootReceiptFinalState (arr : Nat → Nat) : AState :=
  arun 0 (rootReceiptMachineFold arr (runtimePrimeCount + 1))
    (rootReceiptEpilogue runtimeProductionCfg)

private theorem runFromArray_of_stages (p : AProgram) (arr : Nat → Nat)
    (s₀ sf out : AState)
    (hInit : denoteAInstrs p.arrayLen 0 (initialAStateWithArray arr) p.init =
      some s₀)
    (hLoop : (List.range p.loopCount).foldlM
      (fun st index => denoteAInstrs p.arrayLen index st p.body) s₀ = some sf)
    (hEpi : denoteAInstrs p.arrayLen 0 sf p.epilogue = some out) :
    p.runFromArray arr = some out := by
  have hAfterInit :
      (do
        let st ← (some s₀ : Option AState)
        let st ← (List.range p.loopCount).foldlM
          (fun z index => denoteAInstrs p.arrayLen index z p.body) st
        denoteAInstrs p.arrayLen 0 st p.epilogue) =
      (do
        let st ← (List.range p.loopCount).foldlM
          (fun z index => denoteAInstrs p.arrayLen index z p.body) s₀
        denoteAInstrs p.arrayLen 0 st p.epilogue) := Option.bind_some _ _
  have hAfterLoop :
      (do
        let st ← (some sf : Option AState)
        denoteAInstrs p.arrayLen 0 st p.epilogue) =
      denoteAInstrs p.arrayLen 0 sf p.epilogue := Option.bind_some _ _
  unfold AProgram.runFromArray
  rw [hInit, hAfterInit, hLoop, hAfterLoop, hEpi]

theorem rootReceiptProduction_runFromArray (arr : Nat → Nat) :
    (rootReceiptProgram runtimeProductionCfg).runFromArray arr =
      some (rootReceiptFinalState arr) := by
  have hInit := rootReceiptInit_denote arr
  have hLoop := rootReceiptDenoteFold arr (runtimePrimeCount + 1)
    (Nat.le_refl _)
  have hEpi := denoteAInstrs_eq_arun runtimeProductionCfg.arrayLen 0
    (rootReceiptEpilogue runtimeProductionCfg)
    (rootReceiptMachineFold arr (runtimePrimeCount + 1))
    (rootReceiptEpilogue_defined _)
  exact runFromArray_of_stages (rootReceiptProgram runtimeProductionCfg) arr
    (rootReceiptStartedState arr)
    (rootReceiptMachineFold arr (runtimePrimeCount + 1))
    (rootReceiptFinalState arr) hInit hLoop hEpi

theorem rootReceiptFinalState_zero (arr : Nat → Nat)
    (hok : RootReceiptOK arr) :
    (rootReceiptFinalState arr).regs rrFail = 0 := by
  have hspec := rootReceiptMachineFold_spec arr
    (runtimePrimeCount + 1) (Nat.le_refl _)
  apply rootReceiptEpilogue_zero arr
    (rootReceiptMachineFold arr (runtimePrimeCount + 1)) hspec.2
  · exact hspec.1.trans hok.2.2.2
  · exact hok

theorem rootReceiptFinalState_zero_sound (arr : Nat → Nat)
    (hzero : (rootReceiptFinalState arr).regs rrFail = 0) :
    RootReceiptOK arr := by
  have hspec := rootReceiptMachineFold_spec arr
    (runtimePrimeCount + 1) (Nat.le_refl _)
  have hsound := rootReceiptEpilogue_zero_sound arr
    (rootReceiptMachineFold arr (runtimePrimeCount + 1)) hspec.2
    (by simpa only [rootReceiptFinalState] using hzero)
  exact ⟨hsound.1, hsound.2.1, hsound.2.2.1,
    hspec.1.symm.trans hsound.2.2.2⟩

/-- End-to-end compiled receipt theorem.  The premise is the compact table
property certified by the checker; the conclusion is the actual CompCert
execution returning the accepting word `0`. -/
theorem rootReceiptProduction_compiled_zero (arr : Nat → Nat)
    (base : Int) (mem : Verified.MemFragment.Mem)
    (hBase : BaseOk runtimeProductionCfg.arrayLen base)
    (hCells : ∀ k, k < runtimeProductionCfg.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < runtimeProductionCfg.arrayLen → arr k < M)
    (hok : RootReceiptOK arr) :
    ∃ m,
      Verified.MemFragment.evalMCCSequence
          ((rootReceiptProgram runtimeProductionCfg).initialMCCWithMem base mem)
          (rootReceiptProgram runtimeProductionCfg).compile = some m ∧
      m.env ⟨(rootReceiptProgram runtimeProductionCfg).output + 1⟩ = some 0 := by
  let out := rootReceiptFinalState arr
  have hRun : (rootReceiptProgram runtimeProductionCfg).runFromArray arr =
      some out := rootReceiptProduction_runFromArray arr
  obtain ⟨m, hEval, hRel⟩ :=
    AProgram.evalCC_compile_fromArray
      (rootReceiptProgram runtimeProductionCfg)
      (rootReceiptProgram_wf runtimeProductionCfg) base hBase arr mem hCells
      hCellsLt out hRun
  refine ⟨m, hEval, ?_⟩
  have hreg := hRel.hregs.1 rrFail (by decide)
  have hout : out.regs rrFail = 0 := rootReceiptFinalState_zero arr hok
  rw [hout] at hreg
  change m.env ⟨rrFail + 1⟩ = some (0 : Int)
  exact hreg

/-- Receipt soundness in the direction used by a physical run admission. -/
theorem rootReceiptProduction_compiled_zero_sound (arr : Nat → Nat)
    (base : Int) (mem : Verified.MemFragment.Mem)
    (hBase : BaseOk runtimeProductionCfg.arrayLen base)
    (hCells : ∀ k, k < runtimeProductionCfg.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < runtimeProductionCfg.arrayLen → arr k < M)
    (hzero : Option.bind
      (Verified.MemFragment.evalMCCSequence
        ((rootReceiptProgram runtimeProductionCfg).initialMCCWithMem base mem)
        (rootReceiptProgram runtimeProductionCfg).compile)
      (fun m : Verified.MemFragment.MCCState =>
        m.env ⟨(rootReceiptProgram runtimeProductionCfg).output + 1⟩) = some 0) :
    RootReceiptOK arr := by
  let out := rootReceiptFinalState arr
  have hRun : (rootReceiptProgram runtimeProductionCfg).runFromArray arr =
      some out := rootReceiptProduction_runFromArray arr
  obtain ⟨m, hEval, hRel⟩ :=
    AProgram.evalCC_compile_fromArray
      (rootReceiptProgram runtimeProductionCfg)
      (rootReceiptProgram_wf runtimeProductionCfg) base hBase arr mem hCells
      hCellsLt out hRun
  rw [hEval] at hzero
  have hmachine : m.env ⟨rrFail + 1⟩ = some (0 : Int) := by
    simpa only [rootReceiptProgram, Option.bind_some] using hzero
  have hsource := hRel.hregs.1 rrFail (by decide)
  rw [hmachine] at hsource
  have hout : out.regs rrFail = 0 := by
    have hcast : ((out.regs rrFail : Nat) : Int) = 0 :=
      Option.some.inj hsource.symm
    exact_mod_cast hcast
  exact rootReceiptFinalState_zero_sound arr hout

#print axioms rootReceiptProgram_wf
#print axioms rootChecksumProgram_wf
#print axioms rootReceiptBody_defined
#print axioms rootReceiptBody_hash_run
#print axioms rootReceiptMachineFold_spec
#print axioms rootReceiptDenoteFold
#print axioms rootReceiptEpilogue_zero
#print axioms rootReceiptEpilogue_zero_sound
#print axioms rootReceiptProduction_runFromArray
#print axioms rootReceiptProduction_compiled_zero
#print axioms rootReceiptProduction_compiled_zero_sound

end LeanCompCert.Ports.R2SegSieve

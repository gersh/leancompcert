import LeanCompCert.Ports.PsiRuntimePrimeTableSemantics
import LeanCompCert.Verified.ArrayRegFrame

/-! # Source semantics of the compiled psi prime-table packer

The packer scans the already proved root-mark plane.  These lemmas expose one
compiled round as an append-or-skip operation and are symbolic in the root
bound.  No prime list or production-sized fold is evaluated by Lean. -/

namespace LeanCompCert.Ports.PsiSegSieve

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Ports.ArraySegSieve

def psiRootPackN (index : Nat) : Nat := index + 2

def psiRootPackFlag (m : PsiRuntimeMeta) (s : AState) (index : Nat) : Nat :=
  if s.arr (m.markBase + psiRootPackN index) = 0 then 1 else 0

def psiRootPackTargetAddr (m : PsiRuntimeMeta) (s : AState)
    (index : Nat) : Nat :=
  if psiRootPackFlag m s index = 1 then
    s.regs rWrite + m.cfg.primeBase
  else m.markSink

def psiRootPackRead (m : PsiRuntimeMeta) : List AInstr :=
  [ .scalar (.binop 10 .add .idx (.lit 2))
  , .scalar (.binop 11 .add (.reg 10) (.lit m.markBase))
  , .load 12 11
  , .scalar (.binop 13 .eq (.reg 12) (.lit 0)) ]

def psiRootPackTarget (m : PsiRuntimeMeta) : List AInstr :=
  [ .scalar (.binop 14 .add (.reg rWrite) (.lit m.cfg.primeBase))
  , .scalar (.binop 15 .mul (.reg 13) (.reg 14))
  , .scalar (.binop 16 .sub (.lit 1) (.reg 13))
  , .scalar (.binop 17 .mul (.reg 16) (.lit m.markSink))
  , .scalar (.binop 18 .add (.reg 15) (.reg 17)) ]

def psiRootPackCommit : List AInstr :=
  [ .store 18 10
  , .scalar (.binop rWrite .add (.reg rWrite) (.reg 13))
  , .store 11 rZero ]

theorem psiRootPackBody_blocks (m : PsiRuntimeMeta) :
    psiRootPackBody m =
      psiRootPackRead m ++ (psiRootPackTarget m ++ psiRootPackCommit) := by
  simp [psiRootPackBody, psiRootPackRead, psiRootPackTarget,
    psiRootPackCommit]

theorem psiRootPackN_bounds (m : PsiRuntimeMeta) {index : Nat}
    (hi : index < (psiRootPackProgram m).loopCount) :
    2 ≤ psiRootPackN index ∧ psiRootPackN index ≤ m.root := by
  simp only [psiRootPackN, psiRootPackProgram] at hi ⊢
  omega

/-- Exact effect of one compiled pack round.  `hSlot` is required only when
the input cell is selected; it is the fail-closed table-capacity condition
later supplied by the prefix-count invariant. -/
theorem psiRootPackBody_spec (m : PsiRuntimeMeta) (index : Nat) (s : AState)
    (hArray : m.arrayLen < M)
    (hRootM : m.root < M)
    (hZero : s.regs rZero = 0)
    (hWrite : s.regs rWrite ≤ m.cfg.tableLen)
    (hSlot : psiRootPackFlag m s index = 1 →
      s.regs rWrite < m.cfg.tableLen)
    (hi : index < (psiRootPackProgram m).loopCount) :
    AllDefined m.arrayLen index s (psiRootPackBody m) ∧
      (arun index s (psiRootPackBody m)).regs rWrite =
        s.regs rWrite + psiRootPackFlag m s index ∧
      ∀ x, (arun index s (psiRootPackBody m)).arr x =
        if x = m.markBase + psiRootPackN index then 0
        else if x = psiRootPackTargetAddr m s index then
          psiRootPackN index
        else s.arr x := by
  have hn := psiRootPackN_bounds m hi
  have hnM : psiRootPackN index % M = psiRootPackN index :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hn.2 hRootM)
  have hnRawM : (index + 2) % M = index + 2 := by
    simpa [psiRootPackN] using hnM
  have hmark : m.markBase + psiRootPackN index < m.arrayLen := by
    simp only [PsiRuntimeMeta.arrayLen, PsiRuntimeMeta.markSink]
    omega
  have hmarkM : (m.markBase + psiRootPackN index) % M =
      m.markBase + psiRootPackN index :=
    Nat.mod_eq_of_lt (Nat.lt_trans hmark hArray)
  have hmarkRawM : (index + 2 + m.markBase) % M =
      m.markBase + (index + 2) := by
    simpa [psiRootPackN, Nat.add_comm] using hmarkM
  have hsink : m.markSink < m.arrayLen := by
    simp [PsiRuntimeMeta.arrayLen]
  have hsinkM : m.markSink % M = m.markSink :=
    Nat.mod_eq_of_lt (Nat.lt_trans hsink hArray)
  have hPrimeSlot (w : Nat) (hw : w < m.cfg.tableLen) :
      w + m.cfg.primeBase < m.arrayLen := by
    simp only [PsiRuntimeMeta.arrayLen, PsiRuntimeMeta.markSink,
      PsiRuntimeMeta.markBase, PsiCfg.resultBase, PsiCfg.primeSink,
      PsiCfg.streamSink, PsiCfg.streamBase, PsiCfg.ppBase]
    omega
  have hTableEnd : m.cfg.tableLen + m.cfg.primeBase < m.arrayLen := by
    simp only [PsiRuntimeMeta.arrayLen, PsiRuntimeMeta.markSink,
      PsiRuntimeMeta.markBase, PsiCfg.resultBase, PsiCfg.primeSink,
      PsiCfg.streamSink, PsiCfg.streamBase, PsiCfg.ppBase]
    omega
  have hOneM : 1 % M = 1 := Nat.mod_eq_of_lt (by decide)
  have hPredM : (M - 1) % M = M - 1 := Nat.mod_eq_of_lt (by
    exact Nat.sub_lt (by decide) (by decide))
  have hMsum : 1 + (M - 1) = M := by omega
  have hTableM : m.cfg.tableLen < M := by
    exact Nat.lt_of_le_of_lt
      (Nat.le_add_left m.cfg.tableLen m.cfg.primeBase)
      (Nat.lt_trans (by simpa [Nat.add_comm] using hTableEnd) hArray)
  have hWriteM : s.regs rWrite % M = s.regs rWrite :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hWrite hTableM)
  have hPrimeBaseM : m.cfg.primeBase % M = m.cfg.primeBase := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_of_le_of_lt
      (Nat.le_add_left m.cfg.primeBase m.cfg.tableLen)
      (Nat.lt_trans hTableEnd hArray)
  let sr := arun index s (psiRootPackRead m)
  have sr10 : sr.regs 10 = psiRootPackN index := by
    simp [sr, psiRootPackRead, psiRootPackN, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, RegState.set, hnM]
    exact hnRawM
  have sr11 : sr.regs 11 = m.markBase + psiRootPackN index := by
    simp [sr, psiRootPackRead, psiRootPackN, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, RegState.set, hnRawM,
      hmarkRawM]
  have sr12 : sr.regs 12 = s.arr (m.markBase + psiRootPackN index) := by
    simp [sr, psiRootPackRead, psiRootPackN, arun, astep, sval, sdest,
      denoteOperand, denoteOp, AState.writeReg, RegState.set, hnRawM,
      hmarkRawM]
  have sr13 : sr.regs 13 = psiRootPackFlag m s index := by
    simp [sr, psiRootPackRead, psiRootPackFlag, psiRootPackN, arun, astep,
      sval, sdest, denoteOperand, denoteOp, AState.writeReg, RegState.set,
      hnRawM, hmarkRawM]
  have srWrite : sr.regs rWrite = s.regs rWrite := by
    simp [sr, psiRootPackRead, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, rWrite]
  have srArr : sr.arr = s.arr := by
    simp [sr, psiRootPackRead, arun, astep, AState.writeReg]
  let st := arun index sr (psiRootPackTarget m)
  have st18 : st.regs 18 = psiRootPackTargetAddr m s index := by
    by_cases hf : psiRootPackFlag m s index = 1
    · have hw := hSlot hf
      have hslotM : (s.regs rWrite + m.cfg.primeBase) % M =
          s.regs rWrite + m.cfg.primeBase :=
        Nat.mod_eq_of_lt (Nat.lt_trans (hPrimeSlot _ hw) hArray)
      simp [st, psiRootPackTarget, psiRootPackTargetAddr, arun, astep,
        sval, sdest, denoteOperand, denoteOp, AState.writeReg, RegState.set,
        sr13, srWrite, hf, hslotM, hOneM, hPredM, hMsum, Nat.add_mod,
        Nat.mul_mod, hWriteM, hPrimeBaseM]
    · have hf0 : psiRootPackFlag m s index = 0 := by
        unfold psiRootPackFlag at hf ⊢
        split <;> simp_all
      simp [st, psiRootPackTarget, psiRootPackTargetAddr, arun, astep,
        sval, sdest, denoteOperand, denoteOp, AState.writeReg, RegState.set,
        sr13, srWrite, hf, hf0, hsinkM, hOneM, hPredM, hMsum,
        Nat.add_mod, Nat.mul_mod]
  have st10 : st.regs 10 = psiRootPackN index := by
    simp [st, psiRootPackTarget, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, sr10, rWrite]
  have st11 : st.regs 11 = m.markBase + psiRootPackN index := by
    simp [st, psiRootPackTarget, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, sr11, rWrite]
  have st13 : st.regs 13 = psiRootPackFlag m s index := by
    simp [st, psiRootPackTarget, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, sr13, rWrite]
  have stWrite : st.regs rWrite = s.regs rWrite := by
    calc
      st.regs rWrite = sr.regs rWrite := by
        simp [st, psiRootPackTarget, arun, astep, sval, sdest,
          denoteOperand, denoteOp, AState.writeReg, rWrite]
      _ = s.regs rWrite := srWrite
  have stZero : st.regs rZero = 0 := by
    calc
      st.regs rZero = sr.regs rZero := by
        simp [st, psiRootPackTarget, arun, astep, sval, sdest,
          denoteOperand, denoteOp, AState.writeReg, rZero, rWrite]
      _ = s.regs rZero := by
        simp [sr, psiRootPackRead, arun, astep, sval, sdest,
          denoteOperand, denoteOp, AState.writeReg, rZero]
      _ = 0 := hZero
  have stZero' : st.regs 7 = 0 := by simpa [rZero] using stZero
  have stArr : st.arr = s.arr := by
    simp [st, psiRootPackTarget, arun, astep, AState.writeReg, srArr]
  have htarget : psiRootPackTargetAddr m s index < m.arrayLen := by
    unfold psiRootPackTargetAddr
    split
    · exact hPrimeSlot _ (hSlot ‹psiRootPackFlag m s index = 1›)
    · exact hsink
  have hflagLe : psiRootPackFlag m s index ≤ 1 := by
    unfold psiRootPackFlag
    split <;> omega
  have hWriteBound : s.regs rWrite + psiRootPackFlag m s index < M := by
    by_cases hf : psiRootPackFlag m s index = 1
    · have hw := hSlot hf
      have hlt := Nat.lt_trans (hPrimeSlot _ hw) hArray
      simp [hf] at hlt ⊢
      omega
    · have hf0 : psiRootPackFlag m s index = 0 := by omega
      simpa [hf0] using Nat.lt_of_le_of_lt hWrite hTableM
  have hDefined : AllDefined m.arrayLen index s (psiRootPackBody m) := by
    rw [psiRootPackBody_blocks]
    rw [AllDefined_append]
    refine ⟨?_, ?_⟩
    · simp [psiRootPackRead, AllDefined, ADefined, astep, sval, sdest,
        denoteOperand, denoteOp, AState.writeReg, hnRawM, hmarkRawM, hmark]
      simpa [psiRootPackN] using hmark
    · change AllDefined m.arrayLen index sr
        (psiRootPackTarget m ++ psiRootPackCommit)
      rw [AllDefined_append]
      refine ⟨?_, ?_⟩
      · simp [psiRootPackTarget, AllDefined, ADefined, astep, sval, sdest,
          denoteOperand, denoteOp, sr13, srWrite, rWrite]
      · change AllDefined m.arrayLen index st psiRootPackCommit
        simp [psiRootPackCommit, AllDefined, ADefined, astep, sval, sdest,
          denoteOperand, denoteOp, st18, st11, htarget, hmark, st10,
          st13, stWrite, stZero, hWriteBound, rWrite, rZero,
          AState.writeArr, AState.writeReg]
  refine ⟨hDefined, ?_, ?_⟩
  · rw [psiRootPackBody_blocks]
    simp only [arun_append]
    change (arun index st psiRootPackCommit).regs rWrite = _
    simp [psiRootPackCommit, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, RegState.set, stWrite, st13,
      hWriteBound, rWrite, rZero, AState.writeArr]
    rw [show st.regs 129 = s.regs 129 by simpa [rWrite] using stWrite]
    exact Nat.mod_eq_of_lt hWriteBound
  · intro x
    rw [psiRootPackBody_blocks]
    simp only [arun_append]
    change (arun index st psiRootPackCommit).arr x = _
    simp [psiRootPackCommit, arun, astep, sval, sdest, denoteOperand,
      denoteOp, AState.writeReg, AState.writeArr, st18, st10, st11,
      stZero, stZero', stArr, rWrite, rZero]

theorem psiRootPackBody_zero (m : PsiRuntimeMeta) (index : Nat) (s : AState) :
    (arun index s (psiRootPackBody m)).regs rZero = s.regs rZero := by
  apply arun_frame
  rfl

def psiRootPackCount (m : PsiRuntimeMeta) (arr : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => psiRootPackCount m arr k +
      if arr (m.markBase + psiRootPackN k) = 0 then 1 else 0

@[simp] theorem psiRootPackCount_zero (m : PsiRuntimeMeta) (arr : Nat → Nat) :
    psiRootPackCount m arr 0 = 0 := rfl

@[simp] theorem psiRootPackCount_succ (m : PsiRuntimeMeta) (arr : Nat → Nat)
    (k : Nat) :
    psiRootPackCount m arr (k + 1) = psiRootPackCount m arr k +
      if arr (m.markBase + psiRootPackN k) = 0 then 1 else 0 := rfl

theorem psiRootPackCount_mono (m : PsiRuntimeMeta) (arr : Nat → Nat)
    {a b : Nat} (hab : a ≤ b) :
    psiRootPackCount m arr a ≤ psiRootPackCount m arr b := by
  induction hab with
  | refl => exact Nat.le_refl _
  | @step b _ ih =>
      rw [psiRootPackCount_succ]
      exact Nat.le_add_right_of_le ih

theorem psiRootPackCount_selected_lt (m : PsiRuntimeMeta)
    (arr : Nat → Nat) {a b : Nat} (hab : a < b)
    (ha : arr (m.markBase + psiRootPackN a) = 0) :
    psiRootPackCount m arr a < psiRootPackCount m arr b := by
  have hstep : psiRootPackCount m arr (a + 1) =
      psiRootPackCount m arr a + 1 := by simp [ha]
  calc
    psiRootPackCount m arr a < psiRootPackCount m arr (a + 1) := by
      omega
    _ ≤ psiRootPackCount m arr b :=
      psiRootPackCount_mono m arr (by omega)

def psiRootPackStartedState (arr : Nat → Nat) : AState :=
  arun 0 (initialAStateWithArray arr) psiRootPackInit

def psiRootPackFoldPrefix (m : PsiRuntimeMeta) (arr : Nat → Nat)
    (k : Nat) : AState :=
  (List.range k).foldl (fun state index =>
      arun index state (psiRootPackBody m))
    (psiRootPackStartedState arr)

structure PsiRootPackInvariant (m : PsiRuntimeMeta) (arr : Nat → Nat)
    (k : Nat) (s : AState) : Prop where
  writeEq : s.regs rWrite = psiRootPackCount m arr k
  zeroEq : s.regs rZero = 0
  futureEq : ∀ q, k ≤ q → q < (psiRootPackProgram m).loopCount →
    s.arr (m.markBase + psiRootPackN q) =
      arr (m.markBase + psiRootPackN q)
  tableEq : ∀ q, q < k → arr (m.markBase + psiRootPackN q) = 0 →
    s.arr (m.cfg.primeBase + psiRootPackCount m arr q) =
      psiRootPackN q

theorem psiRootPackStartedState_invariant (m : PsiRuntimeMeta)
    (arr : Nat → Nat) :
    PsiRootPackInvariant m arr 0 (psiRootPackStartedState arr) := by
  constructor
  · simp [psiRootPackStartedState, psiRootPackInit, seedRegs, arun, astep,
      sval, sdest, denoteOperand, denoteOp, AState.writeReg, rWrite, rZero]
  · simp [psiRootPackStartedState, psiRootPackInit, seedRegs, arun, astep,
      sval, sdest, denoteOperand, denoteOp, AState.writeReg, rWrite, rZero]
  · intro q _ _
    simp [psiRootPackStartedState, psiRootPackInit, seedRegs, arun, astep,
      AState.writeReg, initialAStateWithArray]
  · intro q hq
    omega

/-- The complete symbolic prefix invariant of the compiled table packer. -/
theorem psiRootPackFoldPrefix_invariant (m : PsiRuntimeMeta)
    (arr : Nat → Nat) (k : Nat)
    (hArray : m.arrayLen < M) (hRootM : m.root < M)
    (hk : k ≤ (psiRootPackProgram m).loopCount)
    (hCapacity : psiRootPackCount m arr
      (psiRootPackProgram m).loopCount ≤ m.cfg.tableLen) :
    PsiRootPackInvariant m arr k (psiRootPackFoldPrefix m arr k) := by
  induction k with
  | zero =>
      exact psiRootPackStartedState_invariant m arr
  | succ k ih =>
      have hklt : k < (psiRootPackProgram m).loopCount := by omega
      have hkpre : k ≤ (psiRootPackProgram m).loopCount := by omega
      let prev := psiRootPackFoldPrefix m arr k
      have hinv : PsiRootPackInvariant m arr k prev := ih hkpre
      have hcurrent := hinv.futureEq k (Nat.le_refl _) hklt
      have hflag : psiRootPackFlag m prev k =
          if arr (m.markBase + psiRootPackN k) = 0 then 1 else 0 := by
        simp [psiRootPackFlag, hcurrent]
      have hwriteLe : prev.regs rWrite ≤ m.cfg.tableLen := by
        rw [hinv.writeEq]
        exact Nat.le_trans (psiRootPackCount_mono m arr hkpre) hCapacity
      have hslot : psiRootPackFlag m prev k = 1 →
          prev.regs rWrite < m.cfg.tableLen := by
        intro hf
        have hselected : arr (m.markBase + psiRootPackN k) = 0 := by
          rw [hflag] at hf
          split at hf
          · assumption
          · simp at hf
        rw [hinv.writeEq]
        have hlt := psiRootPackCount_selected_lt m arr
          (show k < (psiRootPackProgram m).loopCount by exact hklt) hselected
        exact Nat.lt_of_lt_of_le hlt hCapacity
      have hstep := psiRootPackBody_spec m k prev hArray hRootM
        hinv.zeroEq hwriteLe hslot hklt
      let next := arun k prev (psiRootPackBody m)
      have hfold : psiRootPackFoldPrefix m arr (k + 1) = next := by
        simp [psiRootPackFoldPrefix, prev, next, List.range_succ,
          List.foldl_append]
      rw [hfold]
      have hTableBeforeMark (w : Nat) (hw : w ≤ m.cfg.tableLen) :
          m.cfg.primeBase + w < m.markBase := by
        simp only [PsiRuntimeMeta.markBase, PsiCfg.resultBase,
          PsiCfg.primeSink, PsiCfg.streamSink, PsiCfg.streamBase,
          PsiCfg.ppBase]
        omega
      refine
        { writeEq := ?_
          zeroEq := ?_
          futureEq := ?_
          tableEq := ?_ }
      · rw [hstep.2.1, hinv.writeEq, psiRootPackCount_succ, hflag]
      · exact (psiRootPackBody_zero m k prev).trans hinv.zeroEq
      · intro q hkq hqLoop
        have hqBounds := psiRootPackN_bounds m hqLoop
        rw [hstep.2.2]
        have hneMark : m.markBase + psiRootPackN q ≠
            m.markBase + psiRootPackN k := by
          simp [psiRootPackN]
          omega
        have hneN : psiRootPackN q ≠ psiRootPackN k := by
          simp [psiRootPackN]
          omega
        have hneTarget : m.markBase + psiRootPackN q ≠
            psiRootPackTargetAddr m prev k := by
          unfold psiRootPackTargetAddr
          split
          · have hbefore := hTableBeforeMark (prev.regs rWrite) hwriteLe
            omega
          · simp only [PsiRuntimeMeta.markSink]
            omega
        simp [hneMark, hneN, hneTarget]
        exact hinv.futureEq q (by omega) hqLoop
      · intro q hq hselected
        by_cases hqk : q = k
        · subst q
          rw [hstep.2.2]
          have hflagOne : psiRootPackFlag m prev k = 1 := by
            simp [hflag, hselected]
          have htargetEq : psiRootPackTargetAddr m prev k =
              m.cfg.primeBase + psiRootPackCount m arr k := by
            simp [psiRootPackTargetAddr, hflagOne, hinv.writeEq,
              Nat.add_comm]
          have hneMark : m.cfg.primeBase + psiRootPackCount m arr k ≠
              m.markBase + psiRootPackN k := by
            have hcountLe := Nat.le_trans
              (psiRootPackCount_mono m arr hkpre) hCapacity
            have hbefore := hTableBeforeMark _ hcountLe
            omega
          simp [hneMark, htargetEq]
        · have hqOld : q < k := by omega
          rw [hstep.2.2]
          have hcountQLe : psiRootPackCount m arr q ≤ m.cfg.tableLen :=
            Nat.le_trans (psiRootPackCount_mono m arr
              (Nat.le_trans (Nat.le_of_lt hqOld) hkpre)) hCapacity
          have hbefore := hTableBeforeMark
            (psiRootPackCount m arr q) hcountQLe
          have hneMark : m.cfg.primeBase + psiRootPackCount m arr q ≠
              m.markBase + psiRootPackN k := by omega
          have hneTarget : m.cfg.primeBase + psiRootPackCount m arr q ≠
              psiRootPackTargetAddr m prev k := by
            unfold psiRootPackTargetAddr
            split
            · have hrank := psiRootPackCount_selected_lt m arr hqOld
                hselected
              rw [hinv.writeEq]
              omega
            · simp only [PsiRuntimeMeta.markSink]
              omega
          simp [hneMark, hneTarget]
          exact hinv.tableEq q hqOld hselected

theorem psiRootPackDenoteFold (m : PsiRuntimeMeta) (arr : Nat → Nat)
    (k : Nat) (hArray : m.arrayLen < M) (hRootM : m.root < M)
    (hk : k ≤ (psiRootPackProgram m).loopCount)
    (hCapacity : psiRootPackCount m arr
      (psiRootPackProgram m).loopCount ≤ m.cfg.tableLen) :
    (List.range k).foldlM
        (fun state index => denoteAInstrs m.arrayLen index state
          (psiRootPackBody m))
        (psiRootPackStartedState arr) =
      some (psiRootPackFoldPrefix m arr k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hklt : k < (psiRootPackProgram m).loopCount := by omega
      have hkpre : k ≤ (psiRootPackProgram m).loopCount := by omega
      rw [List.range_succ, List.foldlM_append, ih hkpre]
      have hbind :
          (do
            let state ← (some (psiRootPackFoldPrefix m arr k) : Option AState)
            List.foldlM
              (fun state index => denoteAInstrs m.arrayLen index state
                (psiRootPackBody m)) state [k]) =
          List.foldlM
            (fun state index => denoteAInstrs m.arrayLen index state
              (psiRootPackBody m)) (psiRootPackFoldPrefix m arr k) [k] :=
        Option.bind_some _ _
      rw [hbind]
      have hinv := psiRootPackFoldPrefix_invariant m arr k hArray hRootM
        hkpre hCapacity
      have hcurrent := hinv.futureEq k (Nat.le_refl _) hklt
      have hflag : psiRootPackFlag m (psiRootPackFoldPrefix m arr k) k =
          if arr (m.markBase + psiRootPackN k) = 0 then 1 else 0 := by
        simp [psiRootPackFlag, hcurrent]
      have hwriteLe : (psiRootPackFoldPrefix m arr k).regs rWrite ≤
          m.cfg.tableLen := by
        rw [hinv.writeEq]
        exact Nat.le_trans (psiRootPackCount_mono m arr hkpre) hCapacity
      have hslot :
          psiRootPackFlag m (psiRootPackFoldPrefix m arr k) k = 1 →
            (psiRootPackFoldPrefix m arr k).regs rWrite <
              m.cfg.tableLen := by
        intro hf
        have hselected : arr (m.markBase + psiRootPackN k) = 0 := by
          rw [hflag] at hf
          split at hf
          · assumption
          · simp at hf
        rw [hinv.writeEq]
        exact Nat.lt_of_lt_of_le
          (psiRootPackCount_selected_lt m arr hklt hselected) hCapacity
      have hdef := (psiRootPackBody_spec m k
        (psiRootPackFoldPrefix m arr k) hArray hRootM hinv.zeroEq
        hwriteLe hslot hklt).1
      have hden := denoteAInstrs_eq_arun m.arrayLen k (psiRootPackBody m)
        (psiRootPackFoldPrefix m arr k) hdef
      rw [List.foldlM_cons, hden]
      simp [psiRootPackFoldPrefix, List.range_succ, List.foldl_append]

def psiRootPackLoopState (m : PsiRuntimeMeta) (arr : Nat → Nat) : AState :=
  psiRootPackFoldPrefix m arr (psiRootPackProgram m).loopCount

def psiRootPackedState (m : PsiRuntimeMeta) (arr : Nat → Nat) : AState :=
  arun 0 (psiRootPackLoopState m arr) (psiRootPackProgram m).epilogue

theorem psiRootPackRunFromArray_of_stages (m : PsiRuntimeMeta)
    (arr : Nat → Nat) (s₀ sf out : AState)
    (hInit : denoteAInstrs (psiRootPackProgram m).arrayLen 0
      (initialAStateWithArray arr) (psiRootPackProgram m).init = some s₀)
    (hLoop : (List.range (psiRootPackProgram m).loopCount).foldlM
      (fun state index => denoteAInstrs (psiRootPackProgram m).arrayLen index
        state (psiRootPackProgram m).body) s₀ = some sf)
    (hEpi : denoteAInstrs (psiRootPackProgram m).arrayLen 0 sf
      (psiRootPackProgram m).epilogue = some out) :
    (psiRootPackProgram m).runFromArray arr = some out := by
  have hAfterInit :
      (do
        let state ← (some s₀ : Option AState)
        let state ← (List.range (psiRootPackProgram m).loopCount).foldlM
          (fun z index => denoteAInstrs (psiRootPackProgram m).arrayLen
            index z (psiRootPackProgram m).body) state
        denoteAInstrs (psiRootPackProgram m).arrayLen 0 state
          (psiRootPackProgram m).epilogue) =
      (do
        let state ← (List.range (psiRootPackProgram m).loopCount).foldlM
          (fun z index => denoteAInstrs (psiRootPackProgram m).arrayLen
            index z (psiRootPackProgram m).body) s₀
        denoteAInstrs (psiRootPackProgram m).arrayLen 0 state
          (psiRootPackProgram m).epilogue) := Option.bind_some _ _
  have hAfterLoop :
      (do
        let state ← (some sf : Option AState)
        denoteAInstrs (psiRootPackProgram m).arrayLen 0 state
          (psiRootPackProgram m).epilogue) =
      denoteAInstrs (psiRootPackProgram m).arrayLen 0 sf
        (psiRootPackProgram m).epilogue := Option.bind_some _ _
  unfold AProgram.runFromArray
  rw [hInit, hAfterInit, hLoop, hAfterLoop, hEpi]

theorem psiRootPackProgram_runFromArray (m : PsiRuntimeMeta)
    (arr : Nat → Nat) (hArray : m.arrayLen < M) (hRootM : m.root < M)
    (hCapacity : psiRootPackCount m arr
      (psiRootPackProgram m).loopCount ≤ m.cfg.tableLen) :
    (psiRootPackProgram m).runFromArray arr =
      some (psiRootPackedState m arr) := by
  apply psiRootPackRunFromArray_of_stages m arr
    (psiRootPackStartedState arr) (psiRootPackLoopState m arr)
    (psiRootPackedState m arr)
  · apply denoteAInstrs_eq_arun
    simp [psiRootPackProgram, psiRootPackInit, seedRegs, AllDefined,
      ADefined, astep, sval, sdest, denoteOperand, denoteOp,
      AState.writeReg]
  · exact psiRootPackDenoteFold m arr
      (psiRootPackProgram m).loopCount hArray hRootM (Nat.le_refl _)
      hCapacity
  · apply denoteAInstrs_eq_arun
    have hinv := psiRootPackFoldPrefix_invariant m arr
      (psiRootPackProgram m).loopCount hArray hRootM (Nat.le_refl _)
      hCapacity
    have htarget :
        (psiRootPackLoopState m arr).regs rWrite + m.cfg.primeBase <
          m.arrayLen := by
      rw [show (psiRootPackLoopState m arr).regs rWrite =
          psiRootPackCount m arr (psiRootPackProgram m).loopCount by
        exact hinv.writeEq]
      simp only [PsiRuntimeMeta.arrayLen, PsiRuntimeMeta.markSink,
        PsiRuntimeMeta.markBase, PsiCfg.resultBase, PsiCfg.primeSink,
        PsiCfg.streamSink, PsiCfg.streamBase, PsiCfg.ppBase]
      omega
    have htargetM :
        ((psiRootPackLoopState m arr).regs rWrite + m.cfg.primeBase) % M =
          (psiRootPackLoopState m arr).regs rWrite + m.cfg.primeBase :=
      Nat.mod_eq_of_lt (Nat.lt_trans htarget hArray)
    simp [psiRootPackProgram, psiRootPackEpilogue, AllDefined, ADefined,
      astep, sval, sdest, denoteOperand, denoteOp, AState.writeReg,
      htargetM, htarget]

/-! ## Exact mathematical content of the packed table -/

/-- Every rank strictly below a prefix count has a unique selected source
position at that rank.  This is a symbolic discrete intermediate-value
argument; it never searches the production root interval. -/
theorem psiRootPackCount_rank_exists (m : PsiRuntimeMeta)
    (arr : Nat → Nat) {k rank : Nat}
    (hrank : rank < psiRootPackCount m arr k) :
    ∃ q, q < k ∧ arr (m.markBase + psiRootPackN q) = 0 ∧
      psiRootPackCount m arr q = rank := by
  induction k with
  | zero => simp at hrank
  | succ k ih =>
      by_cases hselected : arr (m.markBase + psiRootPackN k) = 0
      · rw [psiRootPackCount_succ, if_pos hselected] at hrank
        by_cases hbefore : rank < psiRootPackCount m arr k
        · rcases ih hbefore with ⟨q, hq, hsel, hcount⟩
          exact ⟨q, by omega, hsel, hcount⟩
        · have heq : rank = psiRootPackCount m arr k := by omega
          exact ⟨k, by omega, hselected, heq.symm⟩
      · rw [psiRootPackCount_succ, if_neg hselected] at hrank
        rcases ih hrank with ⟨q, hq, hsel, hcount⟩
        exact ⟨q, by omega, hsel, hcount⟩

/-- Every occupied rank of the compiled packed table contains a genuine
prime in `[2, root]`.  The theorem composes the literal marking grid, its
primality proof, and the literal prefix packer. -/
theorem psiRootPackLoopState_rank_prime (m : PsiRuntimeMeta)
    (hDiv : 2 ≤ m.divCap)
    (hArray : m.arrayLen < M)
    (hMarkLoopM : (psiRootMarkProgram m).loopCount < M)
    (hRootM : m.root < M)
    (hDivM : m.divCap < M)
    (hSquareM : m.divCap * m.divCap < M)
    (hCap : m.root < (m.divCap + 1) * (m.divCap + 1))
    (hCapacity : psiRootPackCount m
      (psiRootMarkedState m (fun _ => 0)).arr
      (psiRootPackProgram m).loopCount ≤ m.cfg.tableLen)
    {rank : Nat}
    (hrank : rank < psiRootPackCount m
      (psiRootMarkedState m (fun _ => 0)).arr
      (psiRootPackProgram m).loopCount) :
    ∃ p, LeanCompCert.Verified.PackedSieve.IsPrime p ∧ 2 ≤ p ∧
      p ≤ m.root ∧
      (psiRootPackLoopState m
        (psiRootMarkedState m (fun _ => 0)).arr).arr
          (m.cfg.primeBase + rank) = p := by
  let marked := psiRootMarkedState m (fun _ => 0)
  rcases psiRootPackCount_rank_exists m marked.arr hrank with
    ⟨q, hq, hselected, hcount⟩
  have hbounds := psiRootPackN_bounds m hq
  have hprime : LeanCompCert.Verified.PackedSieve.IsPrime
      (psiRootPackN q) :=
    (psiRootMarkedState_cell_eq_zero_iff_prime m (psiRootPackN q)
      hDiv hArray hMarkLoopM hRootM hDivM hSquareM hCap
      hbounds.1 hbounds.2).mp hselected
  have hinv := psiRootPackFoldPrefix_invariant m marked.arr
    (psiRootPackProgram m).loopCount hArray hRootM (Nat.le_refl _)
    hCapacity
  have htable := hinv.tableEq q hq hselected
  refine ⟨psiRootPackN q, hprime, hbounds.1, hbounds.2, ?_⟩
  rw [hcount] at htable
  exact htable

/-- Conversely, every mathematical prime in `[2, root]` occurs at its exact
compiled prefix-count rank.  Together with
`psiRootPackLoopState_rank_prime`, this is gap-free table coverage without a
Lean-generated prime list. -/
theorem psiRootPackLoopState_covers_prime (m : PsiRuntimeMeta)
    (hDiv : 2 ≤ m.divCap)
    (hArray : m.arrayLen < M)
    (hMarkLoopM : (psiRootMarkProgram m).loopCount < M)
    (hRootM : m.root < M)
    (hDivM : m.divCap < M)
    (hSquareM : m.divCap * m.divCap < M)
    (hCap : m.root < (m.divCap + 1) * (m.divCap + 1))
    (hCapacity : psiRootPackCount m
      (psiRootMarkedState m (fun _ => 0)).arr
      (psiRootPackProgram m).loopCount ≤ m.cfg.tableLen)
    {p : Nat} (hp2 : 2 ≤ p) (hpRoot : p ≤ m.root)
    (hprime : LeanCompCert.Verified.PackedSieve.IsPrime p) :
    ∃ rank, rank < psiRootPackCount m
        (psiRootMarkedState m (fun _ => 0)).arr
        (psiRootPackProgram m).loopCount ∧
      (psiRootPackLoopState m
        (psiRootMarkedState m (fun _ => 0)).arr).arr
          (m.cfg.primeBase + rank) = p := by
  let marked := psiRootMarkedState m (fun _ => 0)
  let q := p - 2
  have hqValue : psiRootPackN q = p := by
    simp [q, psiRootPackN]
    omega
  have hq : q < (psiRootPackProgram m).loopCount := by
    simp [q, psiRootPackProgram]
    omega
  have hselected : marked.arr (m.markBase + psiRootPackN q) = 0 := by
    rw [hqValue]
    exact (psiRootMarkedState_cell_eq_zero_iff_prime m p
      hDiv hArray hMarkLoopM hRootM hDivM hSquareM hCap hp2 hpRoot).mpr
        hprime
  let rank := psiRootPackCount m marked.arr q
  have hrank := psiRootPackCount_selected_lt m marked.arr hq hselected
  have hinv := psiRootPackFoldPrefix_invariant m marked.arr
    (psiRootPackProgram m).loopCount hArray hRootM (Nat.le_refl _)
    hCapacity
  have htable := hinv.tableEq q hq hselected
  refine ⟨rank, hrank, ?_⟩
  simpa [psiRootPackLoopState, marked, rank] using htable.trans hqValue

#print axioms psiRootPackBody_spec
#print axioms psiRootPackFoldPrefix_invariant
#print axioms psiRootPackDenoteFold
#print axioms psiRootPackProgram_runFromArray
#print axioms psiRootPackCount_rank_exists
#print axioms psiRootPackLoopState_rank_prime
#print axioms psiRootPackLoopState_covers_prime

end LeanCompCert.Ports.PsiSegSieve

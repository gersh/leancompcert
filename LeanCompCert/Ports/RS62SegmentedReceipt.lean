import LeanCompCert.Ports.RS62SegmentedPrimeMask
import LeanCompCert.Ports.RS62PrimeMaskLadderOverflow
import LeanCompCert.Verified.ArrayAuditFromArray

/-!
# Physical receipts for compiled RS62 segmented pipelines

One receipt records the exact shared-memory call sequence emitted by
`bench/RS62SegmentedPipelineEmit.lean`: fail-safe mark audit, ordinary mark,
normalization, fail-safe ladder audit, and the two endpoint observations.
Compiler simulation and audit soundness turn that finite machine trace into
the source `loopE` equation.  No segment fold is evaluated in Lean.
-/

namespace LeanCompCert.Ports.RS62SegmentedReceipt

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusRootSchedule
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.RS62SegmentedPrimeMask

abbrev markAuditProgram (c : Cfg) : AProgram :=
  LeanCompCert.Verified.ArrayAudit.auditProgram (program c)

abbrev overflowProgram (c : Cfg) (SL SU : Nat) : AProgram :=
  RS62PrimeMaskLadderOverflow.program c.lo c.segLen SL SU
    RS62PrimeMaskLadderOverflow.rBad

abbrev lowerProgram (c : Cfg) (SL SU : Nat) : AProgram :=
  RS62PrimeMaskLadderOverflow.program c.lo c.segLen SL SU
    RS62PrimeMaskLadder.rLogL

abbrev upperProgram (c : Cfg) (SL SU : Nat) : AProgram :=
  RS62PrimeMaskLadderOverflow.program c.lo c.segLen SL SU
    RS62PrimeMaskLadder.rLogU

abbrev ladderAuditProgram (c : Cfg) (SL SU : Nat) : AProgram :=
  LeanCompCert.Verified.ArrayAudit.auditProgram (overflowProgram c SL SU)

/-- Exact physical trace of one compiled segment. -/
def SegmentReceipt (c : Cfg) (SL SU lower upper : Nat) : Prop :=
  ∃ mMarkAudit mMark mNormalize mLadderAudit mOverflow mLower mUpper : MCCState,
    evalMCCSequence
        ((markAuditProgram c).counterAugment.initialMCCWithMem 0
          (initialMem c.arrayLen 0))
        (markAuditProgram c).rolledCompile = some mMarkAudit ∧
    mMarkAudit.env ⟨(markAuditProgram c).output + 1⟩ = some 0 ∧
    evalMCCSequence
        ((program c).counterAugment.initialMCCWithMem 0
          (initialMem c.arrayLen 0))
        (program c).rolledCompile = some mMark ∧
    evalMCCSequence
        ((normalizeProgram c.segLen).counterAugment.initialMCCWithMem 0
          mMark.mem)
        (normalizeProgram c.segLen).rolledCompile = some mNormalize ∧
    evalMCCSequence
        ((ladderAuditProgram c SL SU).counterAugment.initialMCCWithMem 0
          mNormalize.mem)
        (ladderAuditProgram c SL SU).rolledCompile = some mLadderAudit ∧
    mLadderAudit.env ⟨(ladderAuditProgram c SL SU).output + 1⟩ = some 0 ∧
    evalMCCSequence
        ((overflowProgram c SL SU).counterAugment.initialMCCWithMem 0
          mLadderAudit.mem)
        (overflowProgram c SL SU).rolledCompile = some mOverflow ∧
    mOverflow.env ⟨(overflowProgram c SL SU).output + 1⟩ = some 0 ∧
    evalMCCSequence
        ((lowerProgram c SL SU).counterAugment.initialMCCWithMem 0
          mOverflow.mem)
        (lowerProgram c SL SU).rolledCompile = some mLower ∧
    mLower.env ⟨(lowerProgram c SL SU).output + 1⟩ = some (lower : Int) ∧
    evalMCCSequence
        ((upperProgram c SL SU).counterAugment.initialMCCWithMem 0
          mLower.mem)
        (upperProgram c SL SU).rolledCompile = some mUpper ∧
    mUpper.env ⟨(upperProgram c SL SU).output + 1⟩ = some (upper : Int)

private theorem baseOk_of_bytes {len : Nat} (h : 8 * len ≤ M) :
    BaseOk len 0 := by
  constructor
  · exact Int.le_refl 0
  · simpa only [Int.zero_add] using (Int.ofNat_le.2 h)

private theorem physical_cells_of_run
    (p : AProgram) (hp : p.WF) (hBase : BaseOk p.arrayLen 0)
    (arr : Nat → Nat) (mem : Mem)
    (hCells : ∀ k, k < p.arrayLen →
      mem (cellAddr 0 k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < p.arrayLen → arr k < M)
    (out : AState) (hRun : p.runFromArray arr = some out)
    (m : MCCState)
    (hEval : evalMCCSequence
      (p.counterAugment.initialMCCWithMem 0 mem) p.rolledCompile = some m) :
    ∀ k, k < p.arrayLen →
      m.mem (cellAddr 0 k) = some (((out.arr k : Nat) : Int)) := by
  obtain ⟨out', _hRun', hAgree, hRel⟩ :=
    p.sourceRel_of_rolledCompile_fromArray hp 0 hBase arr mem hCells
      hCellsLt out hRun m hEval
  intro k hk
  rw [hAgree.2]
  exact hRel.hcells k hk

/-- A retained segment receipt proves the exact source recurrence endpoints.
The configuration and word premises are compact finite facts intended for a
separate compiled configuration checker. -/
theorem source_loopE_of_segmentReceipt
    (c : Cfg) (bootBound valid delta SL SU lower upper : Nat)
    (h : SingleMixedPaddedRootSchedule c bootBound valid delta)
    (hBaseEq : (1 + ((c.segLen + delta) % M)) % M = c.lo)
    (hLen : (rootScanMixed c.bootPrimes bootBound 1 valid).length =
      c.tableLen)
    (hBudget : ((rootScanMixed c.bootPrimes bootBound 1 valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hRootSqM : c.rootCap * c.rootCap < M)
    (hSegRootM : c.segLen + c.rootCap < M)
    (hLoSegM : c.lo + c.segLen < M)
    (hAboveRoot : c.rootCap < c.lo)
    (hCovered : c.lo + c.segLen - 1 ≤ c.rootCap * c.rootCap)
    (hn0 : 3 ≤ c.lo) (hSL : SL < M) (hSU : SU < M)
    (hEnd : c.lo + c.segLen ≤ 2 ^ 40)
    (hBytes : 8 * c.arrayLen ≤ M)
    (hReceipt : SegmentReceipt c SL SU lower upper) :
    LeanCompCert.Ports.RS62.loopE isPrimeBool c.segLen c.lo SL SU =
      (lower, upper) := by
  rcases hReceipt with
    ⟨mMarkAudit, mMark, mNormalize, mLadderAudit, mOverflow, mLower, mUpper,
      hMarkAuditEval, hMarkAuditZero, hMarkEval, hNormalizeEval,
      hLadderAuditEval, hLadderAuditZero, hOverflowEval, hOverflowZero,
      hLowerEval, hLowerValue, hUpperEval, hUpperValue⟩
  have hArrayPos : 0 < c.arrayLen := by
    simp [Cfg.arrayLen, Cfg.resultBase]
  have hArrayM : c.arrayLen < M := Nat.lt_of_lt_of_le
    (by have : 0 < c.arrayLen := hArrayPos; omega) hBytes
  have hMarkBase : BaseOk c.arrayLen 0 := baseOk_of_bytes hBytes
  have hZeroCells : ∀ k, k < c.arrayLen →
      initialMem c.arrayLen 0 (cellAddr 0 k) = some ((((0 : Nat)) : Int)) :=
    fun _ hk => initialMem_cell c.arrayLen 0 hk
  have hMarkAuditReceipt : Option.bind
      (evalMCCSequence
        ((markAuditProgram c).counterAugment.initialMCCWithMem 0
          (initialMem c.arrayLen 0))
        (markAuditProgram c).rolledCompile)
      (fun m : MCCState => m.env ⟨(markAuditProgram c).output + 1⟩) =
        some (0 : Int) := by
    rw [hMarkAuditEval]
    exact hMarkAuditZero
  obtain ⟨marked, hMarkRun⟩ :=
    LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
      (program c) (program_wf c) 0 hMarkBase (fun _ => 0)
      (initialMem c.arrayLen 0) hZeroCells (fun _ => M_pos) hArrayPos
      hArrayM hMarkAuditReceipt
  have hMarkedCells := physical_cells_of_run (program c) (program_wf c)
    hMarkBase (fun _ => 0) (initialMem c.arrayLen 0) hZeroCells
    (fun _ _ => M_pos) marked hMarkRun mMark hMarkEval
  have hMarkedWord :=
    LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (program c) (fun _ => 0) (fun _ => M_pos) marked hMarkRun
  have hSegPos : 0 < c.segLen := by
    have := h.firstPrimePos
    have := h.firstPrimeLeLen
    omega
  have hSegM : c.segLen < M := by omega
  have hNormBase : BaseOk c.segLen 0 := baseOk_of_bytes (by
    have hlen : c.segLen ≤ c.arrayLen := by
      simp [Cfg.arrayLen, Cfg.resultBase]
      omega
    exact Nat.le_trans (Nat.mul_le_mul_left 8 hlen) hBytes)
  let normalized := normalizedState marked.arr c.segLen
  have hNormalizeRun :
      (normalizeProgram c.segLen).runFromArray marked.arr = some normalized := by
    simpa only [normalized] using normalize_run marked.arr c.segLen hSegM
  have hNormInputCells : ∀ k, k < c.segLen →
      mMark.mem (cellAddr 0 k) = some (((marked.arr k : Nat) : Int)) :=
    fun k hk => hMarkedCells k (by
      have hlen : c.segLen ≤ c.arrayLen := by
        simp [Cfg.arrayLen, Cfg.resultBase]
        omega
      simpa [program] using Nat.lt_of_lt_of_le hk hlen)
  have hNormalizedCells := physical_cells_of_run (normalizeProgram c.segLen)
    (normalizeProgram_wf c.segLen) hNormBase marked.arr mMark.mem
    hNormInputCells (fun k _ => hMarkedWord.2 k) normalized hNormalizeRun
    mNormalize hNormalizeEval
  have hNormalizedWord :=
    LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (normalizeProgram c.segLen) marked.arr (fun k => hMarkedWord.2 k)
      normalized hNormalizeRun
  have hMask := normalizedRun_maskCorrect c bootBound valid delta h hBaseEq
    hLen hBudget hIdxM hRootSqM hSegRootM hLoSegM hAboveRoot hCovered
    marked normalized hMarkRun hNormalizeRun
  let overflowP := overflowProgram c SL SU
  let lowerP := lowerProgram c SL SU
  let upperP := upperProgram c SL SU
  have hOverflowWF : overflowP.WF :=
    RS62PrimeMaskLadderOverflow.program_wf c.lo c.segLen SL SU
      RS62PrimeMaskLadderOverflow.rBad (by decide)
  have hLowerWF : lowerP.WF :=
    RS62PrimeMaskLadderOverflow.program_wf c.lo c.segLen SL SU
      RS62PrimeMaskLadder.rLogL (by decide)
  have hUpperWF : upperP.WF :=
    RS62PrimeMaskLadderOverflow.program_wf c.lo c.segLen SL SU
      RS62PrimeMaskLadder.rLogU (by decide)
  have hLadderAuditReceipt : Option.bind
      (evalMCCSequence
        ((ladderAuditProgram c SL SU).counterAugment.initialMCCWithMem 0
          mNormalize.mem)
        (ladderAuditProgram c SL SU).rolledCompile)
      (fun m : MCCState => m.env ⟨(ladderAuditProgram c SL SU).output + 1⟩) =
        some (0 : Int) := by
    rw [hLadderAuditEval]
    exact hLadderAuditZero
  obtain ⟨overflowOut, hOverflowRun⟩ :=
    LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
      overflowP hOverflowWF 0 hNormBase normalized.arr mNormalize.mem
      hNormalizedCells (fun k => hNormalizedWord.2 k) hSegPos hSegM
      hLadderAuditReceipt
  have hAuditBase : BaseOk (ladderAuditProgram c SL SU).arrayLen 0 := by
    simpa [ladderAuditProgram, overflowP, overflowProgram,
      RS62PrimeMaskLadderOverflow.program,
      LeanCompCert.Verified.ArrayAudit.auditProgram] using hNormBase
  let auditOut :=
    let entry := arun 0 (initialAStateWithArray normalized.arr)
      (LeanCompCert.Verified.ArrayAudit.auditBlock overflowP.arrayLen
        overflowP.regCount overflowP.init)
    let loopOut := (List.range overflowP.loopCount).foldl (fun s idx =>
      arun idx s (LeanCompCert.Verified.ArrayAudit.auditBlock overflowP.arrayLen
        overflowP.regCount overflowP.body)) entry
    arun 0 loopOut (LeanCompCert.Verified.ArrayAudit.auditBlock overflowP.arrayLen
      overflowP.regCount overflowP.epilogue)
  have hAuditRun : (ladderAuditProgram c SL SU).runFromArray normalized.arr =
      some auditOut := by
    simpa only [ladderAuditProgram, overflowP, auditOut] using
      LeanCompCert.Verified.ArrayAudit.auditProgram_runFromArray overflowP
        hOverflowWF normalized.arr (fun k => hNormalizedWord.2 k) hSegPos hSegM
  have hAuditCellsRaw := physical_cells_of_run
    (ladderAuditProgram c SL SU)
    (LeanCompCert.Verified.ArrayAudit.auditProgram_wf overflowP hOverflowWF)
    hAuditBase normalized.arr mNormalize.mem hNormalizedCells
    (fun k _ => hNormalizedWord.2 k) auditOut hAuditRun mLadderAudit
    hLadderAuditEval
  have hAuditZero : auditOut.regs
      (LeanCompCert.Verified.ArrayAudit.auditReg overflowP.regCount) = 0 := by
    apply AProgram.output_eq_of_rolledCompile_fromArray
      (ladderAuditProgram c SL SU)
      (LeanCompCert.Verified.ArrayAudit.auditProgram_wf overflowP hOverflowWF)
      0 hAuditBase normalized.arr mNormalize.mem hNormalizedCells
      (fun k _ => hNormalizedWord.2 k) auditOut hAuditRun 0
    exact hLadderAuditReceipt
  have hAuditSound :=
    LeanCompCert.Verified.ArrayAudit.auditProgram_zero_sound_fromArray overflowP
      hOverflowWF normalized.arr (fun k => hNormalizedWord.2 k) hSegPos hSegM
      hAuditZero
  have hOverflowOutArr : overflowOut.arr = normalized.arr := by
    have hout := AProgram.eq_arun_of_runFromArray_eq_some overflowP
      normalized.arr overflowOut hOverflowRun
    have houtEq : overflowOut =
        RS62PrimeMaskLadderOverflow.machineFoldState normalized.arr c.lo
          c.segLen SL SU := by
      simpa [overflowP, overflowProgram, RS62PrimeMaskLadderOverflow.program,
        RS62PrimeMaskLadderOverflow.machineFoldState, arun] using hout
    rw [houtEq, RS62PrimeMaskLadderOverflow.machineFoldState_arr]
  have hAuditArr : auditOut.arr = normalized.arr := by
    have hAgree := hAuditSound.2
    have hFinalEq :
        (let sEntry := arun 0 (initialAStateWithArray normalized.arr) overflowP.init
         let sLoop := (List.range overflowP.loopCount).foldl
           (fun s idx => arun idx s overflowP.body) sEntry
         arun 0 sLoop overflowP.epilogue) = overflowOut := by
      have hs := hAuditSound.1
      rw [hOverflowRun] at hs
      exact (Option.some.inj hs).symm
    have hAuditSourceArr : auditOut.arr =
        (let sEntry := arun 0 (initialAStateWithArray normalized.arr)
          overflowP.init
         let sLoop := (List.range overflowP.loopCount).foldl
           (fun s idx => arun idx s overflowP.body) sEntry
         arun 0 sLoop overflowP.epilogue).arr := by
      simpa only [auditOut] using hAgree.1
    rw [hAuditSourceArr, hFinalEq, hOverflowOutArr]
  have hLadderAuditCells : ∀ k, k < c.segLen →
      mLadderAudit.mem (cellAddr 0 k) =
        some (((normalized.arr k : Nat) : Int)) := by
    intro k hk
    rw [← hAuditArr]
    exact hAuditCellsRaw k (by
      simpa [ladderAuditProgram, overflowP, overflowProgram,
        RS62PrimeMaskLadderOverflow.program,
        LeanCompCert.Verified.ArrayAudit.auditProgram] using hk)
  have hOverflowReceipt : Option.bind
      (evalMCCSequence
        (overflowP.counterAugment.initialMCCWithMem 0 mLadderAudit.mem)
        overflowP.rolledCompile)
      (fun m : MCCState => m.env ⟨overflowP.output + 1⟩) =
        some (0 : Int) := by
    rw [hOverflowEval]
    exact hOverflowZero
  have hOverflowObserved :
      overflowOut.regs RS62PrimeMaskLadderOverflow.rBad = 0 := by
    exact AProgram.output_eq_of_rolledCompile_fromArray overflowP hOverflowWF
      0 hNormBase normalized.arr mLadderAudit.mem hLadderAuditCells
      (fun k _ => hNormalizedWord.2 k) overflowOut hOverflowRun 0
      hOverflowReceipt
  have hSource := RS62PrimeMaskLadderOverflow.source_loopE_of_runFromArray_zero
    isPrimeBool normalized.arr c.lo c.segLen SL SU hn0 hSL hSU hSegM hEnd
    hMask overflowOut hOverflowRun hOverflowObserved
  have hOverflowCells := physical_cells_of_run overflowP hOverflowWF
    hNormBase normalized.arr mLadderAudit.mem hLadderAuditCells
    (fun k _ => hNormalizedWord.2 k) overflowOut hOverflowRun mOverflow
    hOverflowEval
  have hLowerInputCells : ∀ k, k < c.segLen →
      mOverflow.mem (cellAddr 0 k) =
        some (((normalized.arr k : Nat) : Int)) := by
    intro k hk
    rw [← hSource.2.2.2]
    exact hOverflowCells k (by
      simpa [overflowP, overflowProgram, RS62PrimeMaskLadderOverflow.program]
        using hk)
  have hLowerRun : lowerP.runFromArray normalized.arr = some overflowOut := by
    simpa [lowerP, overflowP, lowerProgram, overflowProgram,
      RS62PrimeMaskLadderOverflow.program, AProgram.runFromArray] using
      hOverflowRun
  have hLowerReceipt : Option.bind
      (evalMCCSequence
        (lowerP.counterAugment.initialMCCWithMem 0 mOverflow.mem)
        lowerP.rolledCompile)
      (fun m : MCCState => m.env ⟨lowerP.output + 1⟩) =
        some (lower : Int) := by
    rw [hLowerEval]
    exact hLowerValue
  have hLowerObserved : overflowOut.regs RS62PrimeMaskLadder.rLogL = lower := by
    exact AProgram.output_eq_of_rolledCompile_fromArray lowerP hLowerWF 0
      hNormBase normalized.arr mOverflow.mem hLowerInputCells
      (fun k _ => hNormalizedWord.2 k) overflowOut hLowerRun lower hLowerReceipt
  have hLowerCells := physical_cells_of_run lowerP hLowerWF hNormBase
    normalized.arr mOverflow.mem hLowerInputCells
    (fun k _ => hNormalizedWord.2 k) overflowOut hLowerRun mLower hLowerEval
  have hUpperInputCells : ∀ k, k < c.segLen →
      mLower.mem (cellAddr 0 k) = some (((normalized.arr k : Nat) : Int)) := by
    intro k hk
    rw [← hSource.2.2.2]
    exact hLowerCells k (by
      simpa [lowerP, lowerProgram, RS62PrimeMaskLadderOverflow.program]
        using hk)
  have hUpperRun : upperP.runFromArray normalized.arr = some overflowOut := by
    simpa [upperP, lowerP, upperProgram, lowerProgram,
      RS62PrimeMaskLadderOverflow.program, AProgram.runFromArray] using hLowerRun
  have hUpperReceipt : Option.bind
      (evalMCCSequence
        (upperP.counterAugment.initialMCCWithMem 0 mLower.mem)
        upperP.rolledCompile)
      (fun m : MCCState => m.env ⟨upperP.output + 1⟩) =
        some (upper : Int) := by
    rw [hUpperEval]
    exact hUpperValue
  have hUpperObserved : overflowOut.regs RS62PrimeMaskLadder.rLogU = upper := by
    exact AProgram.output_eq_of_rolledCompile_fromArray upperP hUpperWF 0
      hNormBase normalized.arr mLower.mem hUpperInputCells
      (fun k _ => hNormalizedWord.2 k) overflowOut hUpperRun upper hUpperReceipt
  apply Prod.ext
  · exact hSource.2.1.symm.trans hLowerObserved
  · exact hSource.2.2.1.symm.trans hUpperObserved

#print axioms source_loopE_of_segmentReceipt

end LeanCompCert.Ports.RS62SegmentedReceipt

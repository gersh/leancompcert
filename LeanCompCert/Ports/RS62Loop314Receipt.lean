import LeanCompCert.Ports.RS62Loop314Bounds
import LeanCompCert.Ports.RS62SegmentedPrimeMask
import LeanCompCert.Verified.ArrayAuditFromArray

/-!
# Physical CompCert receipts for the RS62 equation-(3.14) verifier

The receipt follows the production driver: audit and execute the segmented
prime-mask producer, normalize its cells, audit the equation-(3.14) consumer,
and observe its five result registers.  All range-dependent work is in the
generated CompCert C.  The theorem below connects that physical trace to the
symbolic source recurrence.
-/

namespace LeanCompCert.Ports.RS62Loop314Receipt

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
open LeanCompCert.Ports.RS62Loop314Program
open LeanCompCert.Ports.RS62Loop314Sound

abbrev markAuditProgram (c : Cfg) : AProgram :=
  LeanCompCert.Verified.ArrayAudit.auditProgram
    (RS62SegmentedPrimeMask.program c)

abbrev consumerProgram (c : Cfg) (SL SU accLo accHi outReg : Nat) : AProgram :=
  RS62Loop314Program.program c.lo c.segLen SL SU accLo accHi outReg

abbrev consumerAuditProgram (c : Cfg) (SL SU accLo accHi : Nat) : AProgram :=
  LeanCompCert.Verified.ArrayAudit.auditProgram
    (consumerProgram c SL SU accLo accHi rBad)

/-- Exact physical trace recorded by one production segment. -/
def SegmentReceipt (c : Cfg) (SL SU accLo accHi bad logL logU outLo outHi : Nat) :
    Prop :=
  ∃ mMarkAudit mMark mNormalize mConsumerAudit mBad mLogL mLogU mAccLo mAccHi :
      MCCState,
    evalMCCSequence
        ((markAuditProgram c).counterAugment.initialMCCWithMem 0
          (initialMem c.arrayLen 0))
        (markAuditProgram c).rolledCompile = some mMarkAudit ∧
    mMarkAudit.env ⟨(markAuditProgram c).output + 1⟩ = some 0 ∧
    evalMCCSequence
        ((RS62SegmentedPrimeMask.program c).counterAugment.initialMCCWithMem 0
          (initialMem c.arrayLen 0))
        (RS62SegmentedPrimeMask.program c).rolledCompile = some mMark ∧
    evalMCCSequence
        ((normalizeProgram c.segLen).counterAugment.initialMCCWithMem 0 mMark.mem)
        (normalizeProgram c.segLen).rolledCompile = some mNormalize ∧
    evalMCCSequence
        ((consumerAuditProgram c SL SU accLo accHi).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerAuditProgram c SL SU accLo accHi).rolledCompile =
          some mConsumerAudit ∧
    mConsumerAudit.env ⟨(consumerAuditProgram c SL SU accLo accHi).output + 1⟩ =
      some 0 ∧
    evalMCCSequence
        ((consumerProgram c SL SU accLo accHi rBad).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerProgram c SL SU accLo accHi rBad).rolledCompile = some mBad ∧
    mBad.env ⟨(consumerProgram c SL SU accLo accHi rBad).output + 1⟩ =
      some (bad : Int) ∧
    evalMCCSequence
        ((consumerProgram c SL SU accLo accHi rLogL).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerProgram c SL SU accLo accHi rLogL).rolledCompile = some mLogL ∧
    mLogL.env ⟨(consumerProgram c SL SU accLo accHi rLogL).output + 1⟩ =
      some (logL : Int) ∧
    evalMCCSequence
        ((consumerProgram c SL SU accLo accHi rLogU).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerProgram c SL SU accLo accHi rLogU).rolledCompile = some mLogU ∧
    mLogU.env ⟨(consumerProgram c SL SU accLo accHi rLogU).output + 1⟩ =
      some (logU : Int) ∧
    evalMCCSequence
        ((consumerProgram c SL SU accLo accHi rAccLo).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerProgram c SL SU accLo accHi rAccLo).rolledCompile = some mAccLo ∧
    mAccLo.env ⟨(consumerProgram c SL SU accLo accHi rAccLo).output + 1⟩ =
      some (outLo : Int) ∧
    evalMCCSequence
        ((consumerProgram c SL SU accLo accHi rAccHi).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerProgram c SL SU accLo accHi rAccHi).rolledCompile = some mAccHi ∧
    mAccHi.env ⟨(consumerProgram c SL SU accLo accHi rAccHi).output + 1⟩ =
      some (outHi : Int)

theorem baseOk_of_bytes {len : Nat} (h : 8 * len ≤ M) :
    BaseOk len 0 := by
  constructor
  · exact Int.le_refl 0
  · simpa only [Int.zero_add] using (Int.ofNat_le.2 h)

theorem physical_cells_of_run
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
  obtain ⟨_out', _hRun', hAgree, hRel⟩ :=
    p.sourceRel_of_rolledCompile_fromArray hp 0 hBase arr mem hCells
      hCellsLt out hRun m hEval
  intro k hk
  rw [hAgree.2]
  exact hRel.hcells k hk

theorem output_eq_of_eval
    (p : AProgram) (hp : p.WF) (hBase : BaseOk p.arrayLen 0)
    (arr : Nat → Nat) (mem : Mem)
    (hCells : ∀ k, k < p.arrayLen →
      mem (cellAddr 0 k) = some (((arr k : Nat) : Int)))
    (hCellsLt : ∀ k, k < p.arrayLen → arr k < M)
    (out : AState) (hRun : p.runFromArray arr = some out)
    (m : MCCState) (value : Nat)
    (hEval : evalMCCSequence
      (p.counterAugment.initialMCCWithMem 0 mem) p.rolledCompile = some m)
    (hValue : m.env ⟨p.output + 1⟩ = some (value : Int)) :
    out.regs p.output = value := by
  apply AProgram.output_eq_of_rolledCompile_fromArray p hp 0 hBase arr mem
    hCells hCellsLt out hRun value
  rw [hEval]
  exact hValue

/-- A retained production trace proves the exact equation-(3.14) source fold.
Only compact schedule and coarse endpoint inequalities remain as premises. -/
theorem source_loop314_of_segmentReceipt
    (c : Cfg) (bootBound valid delta SL SU accLo accHi
      logL logU outLo outHi : Nat)
    (h : SingleMixedPaddedRootSchedule c bootBound valid delta)
    (hBaseEq : (1 + ((c.segLen + delta) % M)) % M = c.lo)
    (hLen : (rootScanMixed c.bootPrimes bootBound 1 valid).length = c.tableLen)
    (hBudget : ((rootScanMixed c.bootPrimes bootBound 1 valid).map
      fun p => c.segLen / p + 2).sum ≤ c.markSteps)
    (hIdxM : c.rootSpan + c.markSteps < M)
    (hRootSqM : c.rootCap * c.rootCap < M)
    (hSegRootM : c.segLen + c.rootCap < M)
    (hLoSegM : c.lo + c.segLen < M)
    (hAboveRoot : c.rootCap < c.lo)
    (hCovered : c.lo + c.segLen - 1 ≤ c.rootCap * c.rootCap)
    (hn0 : 2003 ≤ c.lo)
    (hEnd : c.lo + c.segLen ≤ 2 ^ 40)
    (hRhsEnd : (c.lo + c.segLen) * 4294967296 <
      LeanCompCert.Verified.MulWide.B64)
    (hSL : SL < M) (hSU : SU < M) (hLo : accLo < M) (hHi : accHi < M)
    (hSUPos : 0 < SU)
    (hBytes : 8 * c.arrayLen ≤ M)
    (hLogLRoom : SL + c.segLen * (RS62.fpD / (c.lo - 1)) < M)
    (hLogURoom : SU + c.segLen *
      ((RS62.fpD + c.lo + c.segLen) / (c.lo - 1)) < M)
    (hTwiceRoom : 2 * (SU + c.segLen *
      ((RS62.fpD + c.lo + c.segLen) / (c.lo - 1))) < M)
    (hAccRoom : RS62Loop314Sound.wval (accLo, accHi) +
      c.segLen * (SL + c.segLen * (RS62.fpD / (c.lo - 1))) <
        LeanCompCert.Verified.AddWide.B128)
    (hReceipt : SegmentReceipt c SL SU accLo accHi 0 logL logU outLo outHi) :
    RS62Loop314Sound.loop314 isPrimeBool c.segLen c.lo SL SU
        (RS62Loop314Sound.wval (accLo, accHi)) =
      some (logL, logU, RS62Loop314Sound.wval (outLo, outHi)) := by
  rcases hReceipt with
    ⟨mMarkAudit, mMark, mNormalize, mConsumerAudit, mBad, mLogL, mLogU,
      mAccLo, mAccHi, hMarkAuditEval, hMarkAuditZero, hMarkEval,
      hNormalizeEval, hConsumerAuditEval, hConsumerAuditZero,
      hBadEval, hBadValue, hLogLEval, hLogLValue, hLogUEval, hLogUValue,
      hAccLoEval, hAccLoValue, hAccHiEval, hAccHiValue⟩
  have hArrayPos : 0 < c.arrayLen := by simp [Cfg.arrayLen, Cfg.resultBase]
  have hArrayM : c.arrayLen < M := by omega
  have hMarkBase : BaseOk c.arrayLen 0 := baseOk_of_bytes hBytes
  have hZeroCells : ∀ k, k < c.arrayLen →
      initialMem c.arrayLen 0 (cellAddr 0 k) = some ((((0 : Nat)) : Int)) :=
    fun _ hk => initialMem_cell c.arrayLen 0 hk
  have hMarkAuditReceipt : Option.bind
      (evalMCCSequence
        ((markAuditProgram c).counterAugment.initialMCCWithMem 0
          (initialMem c.arrayLen 0)) (markAuditProgram c).rolledCompile)
      (fun m : MCCState => m.env ⟨(markAuditProgram c).output + 1⟩) =
        some (0 : Int) := by
    rw [hMarkAuditEval]
    exact hMarkAuditZero
  obtain ⟨marked, hMarkRun⟩ :=
    LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
      (RS62SegmentedPrimeMask.program c)
      (RS62SegmentedPrimeMask.program_wf c) 0 hMarkBase (fun _ => 0)
      (initialMem c.arrayLen 0) hZeroCells (fun _ => M_pos) hArrayPos
      hArrayM hMarkAuditReceipt
  have hMarkedCells := physical_cells_of_run
    (RS62SegmentedPrimeMask.program c) (RS62SegmentedPrimeMask.program_wf c)
    hMarkBase (fun _ => 0) (initialMem c.arrayLen 0) hZeroCells
    (fun _ _ => M_pos) marked hMarkRun mMark hMarkEval
  have hMarkedWord :=
    LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (RS62SegmentedPrimeMask.program c) (fun _ => 0) (fun _ => M_pos)
      marked hMarkRun
  have hSegPos : 0 < c.segLen := by
    have := h.firstPrimePos
    have := h.firstPrimeLeLen
    omega
  have hSegM : c.segLen < M := by omega
  have hNormBase : BaseOk c.segLen 0 := baseOk_of_bytes (by
    have hlen : c.segLen ≤ c.arrayLen := by simp [Cfg.arrayLen, Cfg.resultBase]; omega
    exact Nat.le_trans (Nat.mul_le_mul_left 8 hlen) hBytes)
  let normalized := normalizedState marked.arr c.segLen
  have hNormalizeRun :
      (normalizeProgram c.segLen).runFromArray marked.arr = some normalized := by
    simpa only [normalized] using normalize_run marked.arr c.segLen hSegM
  have hNormInputCells : ∀ k, k < c.segLen →
      mMark.mem (cellAddr 0 k) = some (((marked.arr k : Nat) : Int)) := by
    intro k hk
    exact hMarkedCells k (by
      have hlen : c.segLen ≤ c.arrayLen := by simp [Cfg.arrayLen, Cfg.resultBase]; omega
      exact Nat.lt_of_lt_of_le hk hlen)
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
  let badP := consumerProgram c SL SU accLo accHi rBad
  have hBadWF : badP.WF := RS62Loop314Program.program_wf
    c.lo c.segLen SL SU accLo accHi rBad (by decide)
  have hConsumerAuditReceipt : Option.bind
      (evalMCCSequence
        ((consumerAuditProgram c SL SU accLo accHi).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerAuditProgram c SL SU accLo accHi).rolledCompile)
      (fun m : MCCState =>
        m.env ⟨(consumerAuditProgram c SL SU accLo accHi).output + 1⟩) =
        some (0 : Int) := by
    rw [hConsumerAuditEval]
    exact hConsumerAuditZero
  obtain ⟨out, hBadRun⟩ :=
    LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
      badP hBadWF 0 hNormBase normalized.arr mNormalize.mem hNormalizedCells
      (fun k => hNormalizedWord.2 k) hSegPos hSegM hConsumerAuditReceipt
  have hClean : out.regs rBad = 0 := by
    exact output_eq_of_eval badP hBadWF hNormBase normalized.arr mNormalize.mem
      hNormalizedCells (fun k _ => hNormalizedWord.2 k) out hBadRun mBad 0
      hBadEval hBadValue
  have harr : ∀ k, k < c.segLen → normalized.arr k ≤ 1 := by
    intro k hk
    rw [hMask k hk]
    split <;> omega
  have hLCap : ∀ k, k < c.segLen →
      RS62.incLWord (c.lo + k) ≤ RS62.fpD / (c.lo - 1) := by
    intro k hk
    exact RS62Loop314Bounds.incLWord_le_segmentCap c.lo c.segLen k
      (by omega) hk
  have hUCap : ∀ k, k < c.segLen →
      RS62.incUWord (c.lo + k) ≤
        (RS62.fpD + c.lo + c.segLen) / (c.lo - 1) := by
    intro k hk
    exact RS62Loop314Bounds.incUWord_le_segmentCap c.lo c.segLen k
      (by omega) hk
  have hRoomEnd := RS62Loop314Bounds.room_and_endLog_of_coarse_bounds
    normalized.arr c.lo c.segLen (RS62.fpD / (c.lo - 1))
      ((RS62.fpD + c.lo + c.segLen) / (c.lo - 1))
    ⟨SL, SU, RS62Loop314Sound.wval (accLo, accHi)⟩ harr
    hLCap hUCap hSUPos hLogLRoom hLogURoom hTwiceRoom hAccRoom
  have hSource := RS62Loop314Sound.source_loop314_of_runFromArray
    isPrimeBool normalized.arr c.lo c.segLen SL SU accLo accHi rBad out
    (fun k => hNormalizedWord.2 k) hn0 hSegM hLoSegM hEnd hRhsEnd
    hSL hSU hLo hHi hRoomEnd.1 hRoomEnd.2 hMask hBadRun hClean
  have outputRun (r : Nat) :
      (consumerProgram c SL SU accLo accHi r).runFromArray normalized.arr =
        some out := by
    unfold AProgram.runFromArray at hBadRun ⊢
    simpa [consumerProgram, RS62Loop314Program.program, badP] using hBadRun
  have outputWF (r : Nat) (hr : r < RS62Loop314Program.regCount) :
      (consumerProgram c SL SU accLo accHi r).WF :=
    RS62Loop314Program.program_wf c.lo c.segLen SL SU accLo accHi r hr
  have hOutLogL : out.regs rLogL = logL := output_eq_of_eval
    (consumerProgram c SL SU accLo accHi rLogL) (outputWF rLogL (by decide))
    hNormBase normalized.arr mNormalize.mem hNormalizedCells
    (fun k _ => hNormalizedWord.2 k) out (outputRun rLogL) mLogL logL
    hLogLEval hLogLValue
  have hOutLogU : out.regs rLogU = logU := output_eq_of_eval
    (consumerProgram c SL SU accLo accHi rLogU) (outputWF rLogU (by decide))
    hNormBase normalized.arr mNormalize.mem hNormalizedCells
    (fun k _ => hNormalizedWord.2 k) out (outputRun rLogU) mLogU logU
    hLogUEval hLogUValue
  have hOutAccLo : out.regs rAccLo = outLo := output_eq_of_eval
    (consumerProgram c SL SU accLo accHi rAccLo) (outputWF rAccLo (by decide))
    hNormBase normalized.arr mNormalize.mem hNormalizedCells
    (fun k _ => hNormalizedWord.2 k) out (outputRun rAccLo) mAccLo outLo
    hAccLoEval hAccLoValue
  have hOutAccHi : out.regs rAccHi = outHi := output_eq_of_eval
    (consumerProgram c SL SU accLo accHi rAccHi) (outputWF rAccHi (by decide))
    hNormBase normalized.arr mNormalize.mem hNormalizedCells
    (fun k _ => hNormalizedWord.2 k) out (outputRun rAccHi) mAccHi outHi
    hAccHiEval hAccHiValue
  simpa [hOutLogL, hOutLogU, hOutAccLo, hOutAccHi] using hSource

end LeanCompCert.Ports.RS62Loop314Receipt

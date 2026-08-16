import LeanCompCert.Ports.RS62Loop410Sound
import LeanCompCert.Ports.RS62Loop314Receipt

/-!
# Physical CompCert receipt for the RS62 equation-(4.10) verifier

The retained trace constructs and audits a segmented prime mask, normalizes
it to zero/one cells, audits the complete fixed-width consumer, and observes
the bad, logarithm, and rounded-product registers.  The theorem below does no
range computation in Lean: compiler simulation connects that physical trace
to the symbolic fold proved in `RS62Loop410Sound`.
-/

namespace LeanCompCert.Ports.RS62Loop410Receipt

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

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
open LeanCompCert.Ports.RS62Loop410Program
open LeanCompCert.Ports.RS62Loop410Sound

abbrev markAuditProgram (c : Cfg) : AProgram :=
  LeanCompCert.Verified.ArrayAudit.auditProgram
    (RS62SegmentedPrimeMask.program c)

abbrev consumerProgram (c : Cfg) (SL P sqrt0 den0 nm20 outReg : Nat) :
    AProgram :=
  RS62Loop410Program.program c.lo c.segLen SL P sqrt0 den0 nm20 outReg

abbrev consumerAuditProgram (c : Cfg)
    (SL P sqrt0 den0 nm20 : Nat) : AProgram :=
  LeanCompCert.Verified.ArrayAudit.auditProgram
    (consumerProgram c SL P sqrt0 den0 nm20 rBad)

/-- Exact physical trace recorded by the production executable. -/
def SegmentReceipt (c : Cfg) (SL P sqrt0 den0 nm20
    bad logL product : Nat) : Prop :=
  ∃ mMarkAudit mMark mNormalize mConsumerAudit mBad mLogL mProduct : MCCState,
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
        ((consumerAuditProgram c SL P sqrt0 den0 nm20).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerAuditProgram c SL P sqrt0 den0 nm20).rolledCompile =
          some mConsumerAudit ∧
    mConsumerAudit.env
        ⟨(consumerAuditProgram c SL P sqrt0 den0 nm20).output + 1⟩ = some 0 ∧
    evalMCCSequence
        ((consumerProgram c SL P sqrt0 den0 nm20 rBad).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerProgram c SL P sqrt0 den0 nm20 rBad).rolledCompile = some mBad ∧
    mBad.env ⟨(consumerProgram c SL P sqrt0 den0 nm20 rBad).output + 1⟩ =
      some (bad : Int) ∧
    evalMCCSequence
        ((consumerProgram c SL P sqrt0 den0 nm20 rLogL).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerProgram c SL P sqrt0 den0 nm20 rLogL).rolledCompile = some mLogL ∧
    mLogL.env ⟨(consumerProgram c SL P sqrt0 den0 nm20 rLogL).output + 1⟩ =
      some (logL : Int) ∧
    evalMCCSequence
        ((consumerProgram c SL P sqrt0 den0 nm20 RS62Loop410Program.rP).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerProgram c SL P sqrt0 den0 nm20 RS62Loop410Program.rP).rolledCompile = some mProduct ∧
    mProduct.env ⟨(consumerProgram c SL P sqrt0 den0 nm20 RS62Loop410Program.rP).output + 1⟩ =
      some (product : Int)

/-- A retained production trace yields the exact rounded source fold and all
strict guard checks, together with the independently proved prime mask. -/
theorem sourceFold_of_segmentReceipt
    (c : Cfg) (bootBound valid delta SL P sqrt0 den0 nm20 logL product : Nat)
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
    (hn0 : 2 ≤ c.lo) (hEnd : c.lo + c.segLen ≤ 100000001)
    (hSL : SL < M) (hP : P < M) (hsqrt0 : sqrt0 < M)
    (hden0 : den0 < M) (hnm20 : nm20 < M)
    (hsqrtInit : sqrt0 = Nat.sqrt c.lo)
    (hdenInit : den0 = c.lo - 1) (hnm2Init : nm20 = c.lo - 2)
    (hBytes : 8 * c.arrayLen ≤ M)
    (hReceipt : SegmentReceipt c SL P sqrt0 den0 nm20 0 logL product) :
    ∃ arr,
      RS62PrimeMaskLadder.MaskCorrect isPrimeBool arr c.lo c.segLen ∧
      let initial : State410 := ⟨SL, SL, P, sqrt0, 0⟩
      let src := sourceFold arr c.lo c.segLen initial
      src.logL = logL ∧ src.product = product ∧ src.bad = 0 ∧
        CellGuards arr c.lo c.segLen initial := by
  rcases hReceipt with
    ⟨mMarkAudit, mMark, mNormalize, mConsumerAudit, mBad, mLogL, mProduct,
      hMarkAuditEval, hMarkAuditZero, hMarkEval, hNormalizeEval,
      hConsumerAuditEval, hConsumerAuditZero, hBadEval, hBadValue,
      hLogLEval, hLogLValue, hProductEval, hProductValue⟩
  have hArrayPos : 0 < c.arrayLen := by simp [Cfg.arrayLen, Cfg.resultBase]
  have hArrayM : c.arrayLen < M := by
    have := hBytes
    omega
  have hMarkBase : BaseOk c.arrayLen 0 :=
    RS62Loop314Receipt.baseOk_of_bytes hBytes
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
  have hMarkedCells := RS62Loop314Receipt.physical_cells_of_run
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
  have hNormBase : BaseOk c.segLen 0 :=
    RS62Loop314Receipt.baseOk_of_bytes (by
      have hlen : c.segLen ≤ c.arrayLen := by
        simp [Cfg.arrayLen, Cfg.resultBase]
        omega
      exact Nat.le_trans (Nat.mul_le_mul_left 8 hlen) hBytes)
  let normalized := normalizedState marked.arr c.segLen
  have hNormalizeRun :
      (normalizeProgram c.segLen).runFromArray marked.arr = some normalized := by
    simpa only [normalized] using normalize_run marked.arr c.segLen hSegM
  have hNormInputCells : ∀ k, k < c.segLen →
      mMark.mem (cellAddr 0 k) = some (((marked.arr k : Nat) : Int)) := by
    intro k hk
    exact hMarkedCells k (by
      have hlen : c.segLen ≤ c.arrayLen := by
        simp [Cfg.arrayLen, Cfg.resultBase]
        omega
      exact Nat.lt_of_lt_of_le hk hlen)
  have hNormalizedCells := RS62Loop314Receipt.physical_cells_of_run
    (normalizeProgram c.segLen) (normalizeProgram_wf c.segLen) hNormBase
    marked.arr mMark.mem hNormInputCells (fun k _ => hMarkedWord.2 k)
    normalized hNormalizeRun mNormalize hNormalizeEval
  have hNormalizedWord :=
    LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (normalizeProgram c.segLen) marked.arr (fun k => hMarkedWord.2 k)
      normalized hNormalizeRun
  have hMask := normalizedRun_maskCorrect c bootBound valid delta h hBaseEq
    hLen hBudget hIdxM hRootSqM hSegRootM hLoSegM hAboveRoot hCovered
    marked normalized hMarkRun hNormalizeRun
  let badP := consumerProgram c SL P sqrt0 den0 nm20 rBad
  have hBadWF : badP.WF := RS62Loop410Program.program_wf
    c.lo c.segLen SL P sqrt0 den0 nm20 rBad (by decide)
  have hConsumerAuditReceipt : Option.bind
      (evalMCCSequence
        ((consumerAuditProgram c SL P sqrt0 den0 nm20).counterAugment.initialMCCWithMem
          0 mNormalize.mem)
        (consumerAuditProgram c SL P sqrt0 den0 nm20).rolledCompile)
      (fun m : MCCState =>
        m.env ⟨(consumerAuditProgram c SL P sqrt0 den0 nm20).output + 1⟩) =
        some (0 : Int) := by
    rw [hConsumerAuditEval]
    exact hConsumerAuditZero
  obtain ⟨out, hBadRun⟩ :=
    LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
      badP hBadWF 0 hNormBase normalized.arr mNormalize.mem hNormalizedCells
      (fun k => hNormalizedWord.2 k) hSegPos hSegM hConsumerAuditReceipt
  have hClean : out.regs rBad = 0 :=
    RS62Loop314Receipt.output_eq_of_eval badP hBadWF hNormBase normalized.arr
      mNormalize.mem hNormalizedCells (fun k _ => hNormalizedWord.2 k)
      out hBadRun mBad 0 hBadEval hBadValue
  have harr : ∀ k, k < c.segLen → normalized.arr k ≤ 1 := by
    intro k hk
    rw [hMask k hk]
    split <;> omega
  have hSource := RS62Loop410Sound.sourceFold_of_runFromArray normalized.arr
    c.lo c.segLen SL P sqrt0 den0 nm20 rBad out
    (fun k => hNormalizedWord.2 k) harr hn0 hSegM hEnd hSL hP hsqrt0
    hden0 hnm20 hsqrtInit hdenInit hnm2Init hBadRun hClean
  have outputRun (r : Nat) :
      (consumerProgram c SL P sqrt0 den0 nm20 r).runFromArray normalized.arr =
        some out := by
    unfold AProgram.runFromArray at hBadRun ⊢
    simpa [consumerProgram, RS62Loop410Program.program, badP] using hBadRun
  have outputWF (r : Nat) (hr : r < RS62Loop410Program.regCount) :
      (consumerProgram c SL P sqrt0 den0 nm20 r).WF :=
    RS62Loop410Program.program_wf c.lo c.segLen SL P sqrt0 den0 nm20 r hr
  have hOutLogL : out.regs rLogL = logL :=
    RS62Loop314Receipt.output_eq_of_eval
      (consumerProgram c SL P sqrt0 den0 nm20 rLogL)
      (outputWF rLogL (by decide)) hNormBase normalized.arr mNormalize.mem
      hNormalizedCells (fun k _ => hNormalizedWord.2 k) out (outputRun rLogL)
      mLogL logL hLogLEval hLogLValue
  have hOutProduct : out.regs RS62Loop410Program.rP = product :=
    RS62Loop314Receipt.output_eq_of_eval
      (consumerProgram c SL P sqrt0 den0 nm20 RS62Loop410Program.rP)
      (outputWF RS62Loop410Program.rP (by decide)) hNormBase normalized.arr mNormalize.mem
      hNormalizedCells (fun k _ => hNormalizedWord.2 k) out (outputRun RS62Loop410Program.rP)
      mProduct product hProductEval hProductValue
  refine ⟨normalized.arr, hMask, ?_⟩
  exact ⟨hSource.1.symm.trans hOutLogL,
    hSource.2.2.1.symm.trans hOutProduct,
    hSource.2.2.2.2.2.1, hSource.2.2.2.2.2.2⟩

#print axioms sourceFold_of_segmentReceipt

end LeanCompCert.Ports.RS62Loop410Receipt

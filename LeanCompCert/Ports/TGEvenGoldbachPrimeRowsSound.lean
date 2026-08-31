import LeanCompCert.Ports.TGEvenGoldbachPrimeRows

/-!
# Exact denotation of the rolled prime-row packer

This file lifts the one-row semantics into a symbolic fold and connects an
accepting source execution to the literal `TGEvenGoldbach.PrimeRowsCorrect`
field.  It does not evaluate a sieve segment or enumerate Goldbach rows.
-/

namespace LeanCompCert.Ports.TGEvenGoldbachPrimeRows

open LeanCompCert
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.InstrBlock
open LeanCompCert.Verified.PackedSieve
open LeanCompCert.Verified.MemFragment

/-- Generic causal seam for a producer which operates on a prefix of a larger
caller-owned allocation.  The fail-safe audit establishes the original
source run at its honest bound.  A separately retained execution of the
array-padded program then relates *every* cell of the larger allocation to
that same source output.  Padding is used only for physical framing; it is not
used to weaken the audit's bounds. -/
theorem source_run_and_full_cells_of_audit_padded_rolled
    (p : AProgram) (hp : p.WF) (fullLen : Nat)
    (hPrefix : p.arrayLen ≤ fullLen) (hlen : 0 < p.arrayLen)
    (hFullM : fullLen < M)
    (arr : Nat → Nat) (harr : ∀ k, arr k < M)
    (base : Int) (hBase : BaseOk fullLen base)
    (mem : Mem)
    (hCells : ∀ k, k < fullLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (hAudit : TGEvenGoldbach.AuditRolledZero p base mem)
    (final : MCCState)
    (hEval : evalMCCSequence
      ((p.padArray fullLen).counterAugment.initialMCCWithMem base mem)
        (p.padArray fullLen).rolledCompile = some final) :
    ∃ out, p.runFromArray arr = some out ∧
      ∀ k, k < fullLen →
        final.mem (cellAddr base k) =
          some (((out.arr k : Nat) : Int)) := by
  have hBasePrefix : BaseOk p.arrayLen base := by
    rcases hBase with ⟨hbase0, hbaseTop⟩
    constructor
    · exact hbase0
    · omega
  have hPrefixM : p.arrayLen < M := Nat.lt_of_le_of_lt hPrefix hFullM
  obtain ⟨out, hRun⟩ :=
    LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
      p hp base hBasePrefix arr mem
        (fun k hk => hCells k (Nat.lt_of_lt_of_le hk hPrefix)) harr hlen
        hPrefixM hAudit
  have hPaddedRun : (p.padArray fullLen).runFromArray arr = some out :=
    p.runFromArray_padArray hPrefix arr out hRun
  obtain ⟨out', _hRun', hAgree, hRel⟩ :=
    (p.padArray fullLen).sourceRel_of_rolledCompile_fromArray
      (p.padArray_wf hp fullLen) base hBase arr mem hCells
      (fun k _ => harr k) out hPaddedRun final hEval
  refine ⟨out, hRun, ?_⟩
  intro k hk
  have hcell := hRel.hcells k hk
  rw [← hAgree.2] at hcell
  exact hcell

/-- The mask and the two witness-value planes end where the two writable bit
planes begin. -/
def Cfg.inputEnd (c : Cfg) : Nat :=
  c.outputBase + c.goldbach.pBitBase

/-- Physical base at which the existing Goldbach scanner sees the packer's
four-plane output suffix. -/
def scannerBase (c : Cfg) (base : Int) : Int :=
  cellAddr base c.outputBase

theorem scannerBase_ok (c : Cfg) (base : Int)
    (hBase : BaseOk c.arrayLen base) :
    BaseOk c.goldbach.arrayLen (scannerBase c base) := by
  rcases hBase with ⟨h0, htop⟩
  constructor
  · unfold scannerBase cellAddr indexedAddr
    omega
  · unfold scannerBase cellAddr indexedAddr
    simp only [Cfg.arrayLen] at htop
    omega

set_option maxRecDepth 40000 in
theorem body_arr_of_ne (c : Cfg) (k : Nat) (s : AState)
    (hready : Ready c s.arr) (hk : k < c.goldbach.count) (i : Nat)
    (hp : i ≠ c.outputBase + c.goldbach.pBitBase + k)
    (hq : i ≠ c.outputBase + c.goldbach.qBitBase + k) :
    (arun k s (body c)).arr i = s.arr i := by
  rcases hready with ⟨_, _, harrayM, _⟩
  have hkM : k < M := by
    simp only [Cfg.arrayLen, TGEvenGoldbach.Cfg.arrayLen] at harrayM
    omega
  have hpBitOutM : c.outputBase + c.goldbach.pBitBase + k < M := by
    simp only [Cfg.arrayLen, TGEvenGoldbach.Cfg.arrayLen] at harrayM
    simp only [TGEvenGoldbach.Cfg.pBitBase]
    omega
  have hqBitOutM : c.outputBase + c.goldbach.qBitBase + k < M := by
    simp only [Cfg.arrayLen, TGEvenGoldbach.Cfg.arrayLen] at harrayM
    simp only [TGEvenGoldbach.Cfg.qBitBase]
    omega
  simp [body, arun, astep, AState.writeReg, AState.writeArr, sdest, sval,
    denoteOperand, denoteOp, rAddr, rOne, Nat.mod_eq_of_lt hkM,
    Nat.mod_eq_of_lt hpBitOutM, Nat.mod_eq_of_lt hqBitOutM, hp, hq]

/-- Every mask and witness-value cell is framed by one packer row. -/
theorem body_input_frame (c : Cfg) (k : Nat) (s : AState)
    (hready : Ready c s.arr) (hk : k < c.goldbach.count) (i : Nat)
    (hi : i < c.inputEnd) :
    (arun k s (body c)).arr i = s.arr i := by
  apply body_arr_of_ne c k s hready hk i <;>
    simp only [Cfg.inputEnd, TGEvenGoldbach.Cfg.pBitBase,
      TGEvenGoldbach.Cfg.qBitBase] at hi ⊢ <;> omega

/-- Rows other than the current row retain both already-written bit cells. -/
theorem body_other_bits (c : Cfg) (k j : Nat) (s : AState)
    (hready : Ready c s.arr) (hk : k < c.goldbach.count)
    (hj : j < c.goldbach.count) (hne : j ≠ k) :
    (arun k s (body c)).arr
        (c.outputBase + c.goldbach.pBitBase + j) =
          s.arr (c.outputBase + c.goldbach.pBitBase + j) ∧
      (arun k s (body c)).arr
        (c.outputBase + c.goldbach.qBitBase + j) =
          s.arr (c.outputBase + c.goldbach.qBitBase + j) := by
  constructor <;> apply body_arr_of_ne c k s hready hk <;>
    simp only [TGEvenGoldbach.Cfg.pBitBase,
      TGEvenGoldbach.Cfg.qBitBase] <;> omega

theorem body_viol_le_one (c : Cfg) (k : Nat) (s : AState)
    (hready : Ready c s.arr) (hk : k < c.goldbach.count)
    (hsbit : s.regs rViol ≤ 1) :
    (arun k s (body c)).regs rViol ≤ 1 := by
  rw [(body_result c s.arr k s hready hk rfl hsbit).1]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hs | hs <;>
    by_cases hrow : RowAccepted c s.arr k <;> simp [hs, hrow]

/-- The only writes are literal one bits, so word readiness is invariant. -/
theorem body_ready (c : Cfg) (k : Nat) (s : AState)
    (hready : Ready c s.arr) (hk : k < c.goldbach.count)
    (hsbit : s.regs rViol ≤ 1) :
    Ready c (arun k s (body c)).arr := by
  have hresult := body_result c s.arr k s hready hk rfl hsbit
  rcases hready with ⟨hseg, hhi, hlen, hwords⟩
  refine ⟨hseg, hhi, hlen, ?_⟩
  intro i hi
  by_cases hp : i = c.outputBase + c.goldbach.pBitBase + k
  · subst i
    rw [hresult.2.1]
    exact (by decide : 1 < M)
  · by_cases hq : i = c.outputBase + c.goldbach.qBitBase + k
    · subst i
      rw [hresult.2.2]
      exact (by decide : 1 < M)
    · rw [body_arr_of_ne c k s ⟨hseg, hhi, hlen, hwords⟩ hk i hp hq]
      exact hwords i hi

/-- `RowAccepted` only observes the mask and the two read-only witness
planes, so agreement up to `inputEnd` is sufficient. -/
theorem rowAccepted_congr_input (c : Cfg) (a b : Nat → Nat) (k : Nat)
    (hk : k < c.goldbach.count)
    (hab : ∀ i, i < c.inputEnd → a i = b i) :
    RowAccepted c a k ↔ RowAccepted c b k := by
  have hpAddr : c.witnessPBase + k < c.inputEnd := by
    simp only [Cfg.witnessPBase, Cfg.inputEnd,
      TGEvenGoldbach.Cfg.pBase, TGEvenGoldbach.Cfg.pBitBase]
    omega
  have hqAddr : c.witnessQBase + k < c.inputEnd := by
    simp only [Cfg.witnessQBase, Cfg.inputEnd,
      TGEvenGoldbach.Cfg.qBase, TGEvenGoldbach.Cfg.pBitBase]
    omega
  have hpw := hab _ hpAddr
  have hqw := hab _ hqAddr
  have hscratch : c.sieve.segLen ≤ c.sieve.arrayLen := by
    simp [LeanCompCert.Ports.ArraySegSieve.Cfg.arrayLen,
      LeanCompCert.Ports.ArraySegSieve.Cfg.resultBase]
    omega
  unfold RowAccepted
  rw [hpw, hqw]
  constructor
  · rintro ⟨hpLo, hpHi, hpBit, hqLo, hqHi, hqBit⟩
    have hpOff : b (c.witnessPBase + k) - c.sieve.lo < c.inputEnd := by
      simp only [Cfg.inputEnd, Cfg.outputBase]
      omega
    have hqOff : b (c.witnessQBase + k) - c.sieve.lo < c.inputEnd := by
      simp only [Cfg.inputEnd, Cfg.outputBase]
      omega
    exact ⟨hpLo, hpHi, (hab _ hpOff).symm.trans hpBit, hqLo, hqHi,
      (hab _ hqOff).symm.trans hqBit⟩
  · rintro ⟨hpLo, hpHi, hpBit, hqLo, hqHi, hqBit⟩
    have hpOff : b (c.witnessPBase + k) - c.sieve.lo < c.inputEnd := by
      simp only [Cfg.inputEnd, Cfg.outputBase]
      omega
    have hqOff : b (c.witnessQBase + k) - c.sieve.lo < c.inputEnd := by
      simp only [Cfg.inputEnd, Cfg.outputBase]
      omega
    exact ⟨hpLo, hpHi, (hab _ hpOff).trans hpBit, hqLo, hqHi,
      (hab _ hqOff).trans hqBit⟩

def packedPrefix (c : Cfg) (arr : Nat → Nat) (f : Nat) : AState :=
  (List.range f).foldl (fun s k => arun k s (body c))
    (initialAStateWithArray arr)

theorem packedPrefix_succ (c : Cfg) (arr : Nat → Nat) (f : Nat) :
    packedPrefix c arr (f + 1) =
      arun f (packedPrefix c arr f) (body c) := by
  unfold packedPrefix
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

structure PrefixInv (c : Cfg) (arr : Nat → Nat) (f : Nat)
    (s : AState) : Prop where
  ready : Ready c s.arr
  viol_le_one : s.regs rViol ≤ 1
  input_frame : ∀ i, i < c.inputEnd → s.arr i = arr i
  zero_iff : s.regs rViol = 0 ↔
    ∀ k, k < f → RowAccepted c arr k
  bits_one : ∀ k, k < f →
    s.arr (c.outputBase + c.goldbach.pBitBase + k) = 1 ∧
      s.arr (c.outputBase + c.goldbach.qBitBase + k) = 1

private theorem initial_viol_zero (arr : Nat → Nat) :
    (initialAStateWithArray arr).regs rViol = 0 := by
  simp [initialAStateWithArray, initialState, rViol]

/-- Symbolic prefix invariant for an arbitrary shard length. -/
theorem packedPrefix_inv (c : Cfg) (arr : Nat → Nat)
    (hready : Ready c arr) (f : Nat) (hf : f ≤ c.goldbach.count) :
    PrefixInv c arr f (packedPrefix c arr f) := by
  induction f with
  | zero =>
      refine ⟨hready, ?_, ?_, ?_, ?_⟩
      · simp [packedPrefix, initial_viol_zero]
      · intro i _
        rfl
      · simp [packedPrefix, initial_viol_zero]
      · intro k hk
        omega
  | succ f ih =>
      have hfCount : f < c.goldbach.count := by omega
      have hprev := ih (by omega)
      rw [packedPrefix_succ]
      let s := packedPrefix c arr f
      have hresult := body_result c s.arr f s hprev.ready hfCount rfl
        hprev.viol_le_one
      have hrow := rowAccepted_congr_input c s.arr arr f hfCount
        hprev.input_frame
      have hstepZero :
          (s.regs rViol |||
              (if RowAccepted c s.arr f then 0 else 1)) = 0 ↔
            s.regs rViol = 0 ∧ RowAccepted c s.arr f := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hprev.viol_le_one with hs | hs
        · have hs' : s.regs rViol = 0 := by simpa only [s] using hs
          by_cases hr : RowAccepted c s.arr f <;> simp [hs', hr]
        · have hs' : s.regs rViol = 1 := by simpa only [s] using hs
          by_cases hr : RowAccepted c s.arr f <;> simp [hs', hr]
      refine ⟨body_ready c f s hprev.ready hfCount hprev.viol_le_one,
        body_viol_le_one c f s hprev.ready hfCount hprev.viol_le_one,
        ?_, ?_, ?_⟩
      · intro i hi
        exact (body_input_frame c f s hprev.ready hfCount i hi).trans
          (hprev.input_frame i hi)
      · rw [hresult.1, hstepZero, hprev.zero_iff, hrow]
        constructor
        · rintro ⟨hall, hfrow⟩ k hk
          by_cases heq : k = f
          · simpa [heq] using hfrow
          · exact hall k (by omega)
        · intro hall
          exact ⟨(fun k hk => hall k (by omega)), hall f (by omega)⟩
      · intro k hk
        by_cases heq : k = f
        · subst k
          exact hresult.2
        · have hkPrev : k < f := by omega
          have hkeep := body_other_bits c f k s hprev.ready hfCount
            (by omega) heq
          exact ⟨hkeep.1.trans (hprev.bits_one k hkPrev).1,
            hkeep.2.trans (hprev.bits_one k hkPrev).2⟩

theorem packedState_eq_prefix (c : Cfg) (arr : Nat → Nat) :
    packedState c arr = packedPrefix c arr c.goldbach.count := rfl

theorem packedState_inv (c : Cfg) (arr : Nat → Nat)
    (hready : Ready c arr) :
    PrefixInv c arr c.goldbach.count (packedState c arr) := by
  rw [packedState_eq_prefix]
  exact packedPrefix_inv c arr hready c.goldbach.count
    (Nat.le_refl c.goldbach.count)

theorem packedPrefix_words_all (c : Cfg) (arr : Nat → Nat)
    (hready : Ready c arr) (hwords : ∀ i, arr i < M)
    (f : Nat) (hf : f ≤ c.goldbach.count) :
    ∀ i, (packedPrefix c arr f).arr i < M := by
  induction f with
  | zero =>
      intro i
      simpa [packedPrefix, initialAStateWithArray] using hwords i
  | succ f ih =>
      have hfCount : f < c.goldbach.count := by omega
      have hprev := packedPrefix_inv c arr hready f (by omega)
      rw [packedPrefix_succ]
      let s := packedPrefix c arr f
      have hresult := body_result c s.arr f s hprev.ready hfCount rfl
        hprev.viol_le_one
      intro i
      by_cases hp : i = c.outputBase + c.goldbach.pBitBase + f
      · subst i
        rw [hresult.2.1]
        exact (by decide : 1 < M)
      · by_cases hq : i = c.outputBase + c.goldbach.qBitBase + f
        · subst i
          rw [hresult.2.2]
          exact (by decide : 1 < M)
        · rw [body_arr_of_ne c f s hprev.ready hfCount i hp hq]
          exact ih (by omega) i

theorem packedState_words_all (c : Cfg) (arr : Nat → Nat)
    (hready : Ready c arr) (hwords : ∀ i, arr i < M) :
    ∀ i, (packedState c arr).arr i < M := by
  rw [packedState_eq_prefix]
  exact packedPrefix_words_all c arr hready hwords c.goldbach.count
    (Nat.le_refl c.goldbach.count)

theorem run_words_all (c : Cfg) (arr : Nat → Nat) (out : AState)
    (hready : Ready c arr) (hwords : ∀ i, arr i < M)
    (hRun : (program c).runFromArray arr = some out) :
    ∀ i, out.arr i < M := by
  rw [run_eq_packedState c arr out hRun]
  exact packedState_words_all c arr hready hwords

/-- Exact primality of both witness values follows from an accepted row and
the segmented sieve's source denotation. -/
theorem primes_of_rowAccepted (c : Cfg) (arr : Nat → Nat) (k : Nat)
    (hmask : RS62PrimeMaskLadder.MaskCorrect
      RS62SegmentedPrimeMask.isPrimeBool arr c.sieve.lo c.sieve.segLen)
    (hrow : RowAccepted c arr k) :
    IsPrime (arr (c.witnessPBase + k)) ∧
      IsPrime (arr (c.witnessQBase + k)) := by
  let p := arr (c.witnessPBase + k)
  let q := arr (c.witnessQBase + k)
  change c.sieve.lo ≤ p ∧ p < c.sieve.lo + c.sieve.segLen ∧
    arr (p - c.sieve.lo) = 1 ∧
    c.sieve.lo ≤ q ∧ q < c.sieve.lo + c.sieve.segLen ∧
    arr (q - c.sieve.lo) = 1 at hrow
  rcases hrow with ⟨hpLo, hpHi, hpBit, hqLo, hqHi, hqBit⟩
  have hpOff : p - c.sieve.lo < c.sieve.segLen := by omega
  have hqOff : q - c.sieve.lo < c.sieve.segLen := by omega
  have hpMask := hmask (p - c.sieve.lo) hpOff
  have hqMask := hmask (q - c.sieve.lo) hqOff
  have hpAdd : c.sieve.lo + (p - c.sieve.lo) = p := by omega
  have hqAdd : c.sieve.lo + (q - c.sieve.lo) = q := by omega
  rw [hpAdd] at hpMask
  rw [hqAdd] at hqMask
  change IsPrime p ∧ IsPrime q
  constructor
  · by_cases hp : IsPrime p
    · exact hp
    · have hone := hpMask.symm.trans hpBit
      simp [RS62SegmentedPrimeMask.isPrimeBool, hp] at hone
  · by_cases hq : IsPrime q
    · exact hq
    · have hone := hqMask.symm.trans hqBit
      simp [RS62SegmentedPrimeMask.isPrimeBool, hq] at hone

/-- Foundation-only signature-to-source theorem.  A zero accepting execution
of the compiled row packer, combined with the exact segmented-prime mask,
produces the literal field consumed by `TGEvenGoldbach.RolledReceipt`. -/
theorem primeRowsCorrect_of_packed_zero (c : Cfg) (arr : Nat → Nat)
    (hready : Ready c arr)
    (hmask : RS62PrimeMaskLadder.MaskCorrect
      RS62SegmentedPrimeMask.isPrimeBool arr c.sieve.lo c.sieve.segLen)
    (hzero : (packedState c arr).regs rViol = 0) :
    TGEvenGoldbach.PrimeRowsCorrect c.goldbach
      (outputArray c (packedState c arr).arr) := by
  have hinv := packedState_inv c arr hready
  have hall := hinv.zero_iff.mp hzero
  intro k hk
  have hrow := hall k hk
  have hprimes := primes_of_rowAccepted c arr k hmask hrow
  have hbits := hinv.bits_one k hk
  have hpAddr : c.outputBase + c.goldbach.pBase + k < c.inputEnd := by
    simp only [Cfg.inputEnd, TGEvenGoldbach.Cfg.pBase,
      TGEvenGoldbach.Cfg.pBitBase]
    omega
  have hqAddr : c.outputBase + c.goldbach.qBase + k < c.inputEnd := by
    simp only [Cfg.inputEnd, TGEvenGoldbach.Cfg.qBase,
      TGEvenGoldbach.Cfg.pBitBase]
    omega
  have hpFinal :
      IsPrime ((packedState c arr).arr
        (c.outputBase + c.goldbach.pBase + k)) := by
    rw [hinv.input_frame _ hpAddr]
    simpa only [Cfg.witnessPBase, Nat.add_assoc] using hprimes.1
  have hqFinal :
      IsPrime ((packedState c arr).arr
        (c.outputBase + c.goldbach.qBase + k)) := by
    rw [hinv.input_frame _ hqAddr]
    simpa only [Cfg.witnessQBase, Nat.add_assoc] using hprimes.2
  constructor
  · constructor
    · intro _
      simpa [outputArray, Nat.add_assoc] using hpFinal
    · intro _
      simpa [outputArray, Nat.add_assoc] using hbits.1
  · constructor
    · intro _
      simpa [outputArray, Nat.add_assoc] using hqFinal
    · intro _
      simpa [outputArray, Nat.add_assoc] using hbits.2

/-- Successful source execution form used by the compiled-signature bridge. -/
theorem primeRowsCorrect_of_run_zero (c : Cfg) (arr : Nat → Nat)
    (out : AState) (hready : Ready c arr)
    (hmask : RS62PrimeMaskLadder.MaskCorrect
      RS62SegmentedPrimeMask.isPrimeBool arr c.sieve.lo c.sieve.segLen)
    (hRun : (program c).runFromArray arr = some out)
    (hzero : out.regs rViol = 0) :
    TGEvenGoldbach.PrimeRowsCorrect c.goldbach (outputArray c out.arr) := by
  have hout := run_eq_packedState c arr out hRun
  subst out
  exact primeRowsCorrect_of_packed_zero c arr hready hmask hzero

/-- Recover the exact mathematical prime mask from external source runs.  The
mark program is allowed to start with populated Goldbach witness planes: only
its declared sieve prefix must be zero.  This is the reusable source boundary
between the segmented-sieve campaign and downstream consumers of the mask. -/
theorem maskCorrect_of_segmented_source_runs
    (c : Cfg) (bootBound valid delta : Nat)
    (hSchedule :
      LeanCompCert.Ports.ArraySegMobiusIndexedFull.SingleMixedPaddedRootSchedule
        c.sieve bootBound valid delta)
    (hBase : (1 + ((c.sieve.segLen + delta) % M)) % M = c.sieve.lo)
    (hTableLen :
      (LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed.rootScanMixed
        c.sieve.bootPrimes bootBound 1 valid).length = c.sieve.tableLen)
    (hBudget :
      ((LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed.rootScanMixed
        c.sieve.bootPrimes bootBound 1 valid).map
          fun p => c.sieve.segLen / p + 2).sum ≤ c.sieve.markSteps)
    (hIdxM : c.sieve.rootSpan + c.sieve.markSteps < M)
    (hRootSqM : c.sieve.rootCap * c.sieve.rootCap < M)
    (hSegRootM : c.sieve.segLen + c.sieve.rootCap < M)
    (hLoSegM : c.sieve.lo + c.sieve.segLen < M)
    (hAboveRoot : c.sieve.rootCap < c.sieve.lo)
    (hCovered : c.sieve.lo + c.sieve.segLen - 1 ≤
      c.sieve.rootCap * c.sieve.rootCap)
    (initial : Nat → Nat) (marked normalized : AState)
    (hZeroPrefix : ∀ j, j < c.sieve.arrayLen → initial j = 0)
    (hMark : (RS62SegmentedPrimeMask.program c.sieve).runFromArray initial =
      some marked)
    (hNormalize :
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).runFromArray
        marked.arr = some normalized) :
    RS62PrimeMaskLadder.MaskCorrect RS62SegmentedPrimeMask.isPrimeBool
      normalized.arr c.sieve.lo c.sieve.segLen := by
  have hScratch : c.sieve.segLen ≤ c.sieve.arrayLen := by
    simp [LeanCompCert.Ports.ArraySegSieve.Cfg.arrayLen,
      LeanCompCert.Ports.ArraySegSieve.Cfg.resultBase]
    omega
  obtain ⟨canonicalMarked, hCanonicalMark, hMarkedAgree⟩ :=
    AProgram.runFromArray_transfer_prefix
      (RS62SegmentedPrimeMask.program c.sieve) initial (fun _ => 0) marked
      (fun j hj => by simpa using hZeroPrefix j hj) hMark
  have hNormalizeInput : ∀ j,
      j < (RS62SegmentedPrimeMask.normalizeProgram
        c.sieve.segLen).arrayLen →
        marked.arr j = canonicalMarked.arr j := by
    intro j hj
    apply hMarkedAgree.2 j
    simpa [RS62SegmentedPrimeMask.program] using
      (Nat.lt_of_lt_of_le hj hScratch)
  obtain ⟨canonicalNormalized, hCanonicalNormalize, hNormalizedAgree⟩ :=
    AProgram.runFromArray_transfer_prefix
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen)
      marked.arr canonicalMarked.arr normalized hNormalizeInput hNormalize
  have hCanonicalMask :=
    RS62SegmentedPrimeMask.normalizedRun_maskCorrect
      c.sieve bootBound valid delta hSchedule hBase hTableLen hBudget hIdxM
      hRootSqM hSegRootM hLoSegM hAboveRoot hCovered canonicalMarked
      canonicalNormalized hCanonicalMark hCanonicalNormalize
  intro k hk
  rw [hNormalizedAgree.2 k (by
    simpa [RS62SegmentedPrimeMask.normalizeProgram] using hk)]
  exact hCanonicalMask k hk

/-- Full source-denotation composition for the producer.  Exact external
segmented-sieve runs supply the mathematical mask; a zero accepting packer run
then supplies the literal `PrimeRowsCorrect` field used by the rolled binary
Goldbach scanner. -/
theorem primeRowsCorrect_of_segmented_source_pipeline
    (c : Cfg) (bootBound valid delta : Nat)
    (hSchedule :
      LeanCompCert.Ports.ArraySegMobiusIndexedFull.SingleMixedPaddedRootSchedule
        c.sieve bootBound valid delta)
    (hBase : (1 + ((c.sieve.segLen + delta) % M)) % M = c.sieve.lo)
    (hTableLen :
      (LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed.rootScanMixed
        c.sieve.bootPrimes bootBound 1 valid).length = c.sieve.tableLen)
    (hBudget :
      ((LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed.rootScanMixed
        c.sieve.bootPrimes bootBound 1 valid).map
          fun p => c.sieve.segLen / p + 2).sum ≤ c.sieve.markSteps)
    (hIdxM : c.sieve.rootSpan + c.sieve.markSteps < M)
    (hRootSqM : c.sieve.rootCap * c.sieve.rootCap < M)
    (hSegRootM : c.sieve.segLen + c.sieve.rootCap < M)
    (hLoSegM : c.sieve.lo + c.sieve.segLen < M)
    (hAboveRoot : c.sieve.rootCap < c.sieve.lo)
    (hCovered : c.sieve.lo + c.sieve.segLen - 1 ≤
      c.sieve.rootCap * c.sieve.rootCap)
    (initial : Nat → Nat) (marked normalized packed : AState)
    (hZeroPrefix : ∀ j, j < c.sieve.arrayLen → initial j = 0)
    (hMark : (RS62SegmentedPrimeMask.program c.sieve).runFromArray initial =
      some marked)
    (hNormalize :
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).runFromArray
        marked.arr = some normalized)
    (hReady : Ready c normalized.arr)
    (hPack : (program c).runFromArray normalized.arr = some packed)
    (hzero : packed.regs rViol = 0) :
    TGEvenGoldbach.PrimeRowsCorrect c.goldbach (outputArray c packed.arr) := by
  have hMask := maskCorrect_of_segmented_source_runs c bootBound valid delta
    hSchedule hBase hTableLen hBudget hIdxM hRootSqM hSegRootM hLoSegM
    hAboveRoot hCovered initial marked normalized hZeroPrefix hMark hNormalize
  exact primeRowsCorrect_of_run_zero c normalized.arr packed hReady hMask
    hPack hzero

/-- Rolled CompCert acceptance form for the packer stage.  The audit
signature supplies source definedness; the ordinary rolled signature supplies
the zero violation word.  No row fold is replayed in this theorem. -/
theorem primeRowsCorrect_of_rolled_acceptance
    (c : Cfg) (arr : Nat → Nat) (hready : Ready c arr)
    (hmask : RS62PrimeMaskLadder.MaskCorrect
      RS62SegmentedPrimeMask.isPrimeBool arr c.sieve.lo c.sieve.segLen)
    (base : Int) (hBase : BaseOk c.arrayLen base)
    (mem : LeanCompCert.Verified.MemFragment.Mem)
    (hCells : ∀ k, k < c.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (harr : ∀ k, arr k < M)
    (hAudit : TGEvenGoldbach.AuditRolledZero (program c) base mem)
    (hAccept : TGEvenGoldbach.RolledResult (program c) base mem 0) :
    ∃ out, (program c).runFromArray arr = some out ∧
      TGEvenGoldbach.PrimeRowsCorrect c.goldbach (outputArray c out.arr) := by
  have hlen : 0 < c.arrayLen := by
    have hseg := hready.1
    have hscratch : c.sieve.segLen ≤ c.sieve.arrayLen := by
      simp [LeanCompCert.Ports.ArraySegSieve.Cfg.arrayLen,
        LeanCompCert.Ports.ArraySegSieve.Cfg.resultBase]
      omega
    simp only [Cfg.arrayLen, Cfg.outputBase,
      TGEvenGoldbach.Cfg.arrayLen]
    omega
  obtain ⟨out, hRun⟩ :=
    LeanCompCert.Verified.ArrayAudit.source_runFromArray_of_audit_rolled_zero
      (program c) (program_wf c) base hBase arr mem hCells harr hlen
      hready.2.2.1 hAudit
  have hzero : out.regs (program c).output = 0 :=
    AProgram.output_eq_of_rolledCompile_fromArray
      (program c) (program_wf c) base hBase arr mem hCells
      (fun k _ => harr k) out hRun 0 hAccept
  refine ⟨out, hRun, primeRowsCorrect_of_run_zero c arr out hready hmask
    hRun ?_⟩
  simpa [program, rViol] using hzero

/-- Retained-state form of the rolled theorem.  Besides the literal
`PrimeRowsCorrect` field, it proves that the *same* logical four-plane array
is represented in the producer's final physical memory at `scannerBase`.
This is the exact field/memory connection needed to start the existing
`TGEvenGoldbach` rolled scanner causally. -/
theorem primeRowsCorrect_and_cells_of_rolled_state
    (c : Cfg) (arr : Nat → Nat) (hready : Ready c arr)
    (hmask : RS62PrimeMaskLadder.MaskCorrect
      RS62SegmentedPrimeMask.isPrimeBool arr c.sieve.lo c.sieve.segLen)
    (base : Int) (hBase : BaseOk c.arrayLen base)
    (mem : LeanCompCert.Verified.MemFragment.Mem)
    (hCells : ∀ k, k < c.arrayLen →
      mem (cellAddr base k) = some (((arr k : Nat) : Int)))
    (harr : ∀ k, arr k < M)
    (hAudit : TGEvenGoldbach.AuditRolledZero (program c) base mem)
    (m : LeanCompCert.Verified.MemFragment.MCCState)
    (hEval : LeanCompCert.Verified.MemFragment.evalMCCSequence
      ((program c).counterAugment.initialMCCWithMem base mem)
        (program c).rolledCompile = some m)
    (hzero : m.env ⟨(program c).output + 1⟩ = some (0 : Int)) :
    ∃ out, (program c).runFromArray arr = some out ∧
      TGEvenGoldbach.PrimeRowsCorrect c.goldbach (outputArray c out.arr) ∧
      (∀ k, k < c.goldbach.arrayLen →
        m.mem (cellAddr (scannerBase c base) k) =
          some ((((outputArray c out.arr k) : Nat) : Int))) := by
  have hAccept : TGEvenGoldbach.RolledResult (program c) base mem 0 := by
    unfold TGEvenGoldbach.RolledResult
    rw [hEval]
    exact hzero
  obtain ⟨out, hRun, hprime⟩ := primeRowsCorrect_of_rolled_acceptance
    c arr hready hmask base hBase mem hCells harr hAudit hAccept
  obtain ⟨out', _hRun', hAgree, hRel⟩ :=
    (program c).sourceRel_of_rolledCompile_fromArray (program_wf c) base
      hBase arr mem hCells (fun k _ => harr k) out hRun m hEval
  refine ⟨out, hRun, hprime, ?_⟩
  intro k hk
  have hi : c.outputBase + k < c.arrayLen := by
    simp only [Cfg.arrayLen]
    omega
  have hcell := hRel.hcells (c.outputBase + k) hi
  rw [← hAgree.2] at hcell
  have haddr : cellAddr (scannerBase c base) k =
      cellAddr base (c.outputBase + k) := by
    unfold scannerBase cellAddr indexedAddr
    omega
  rw [haddr]
  simpa [outputArray, Nat.add_assoc] using hcell

set_option maxRecDepth 40000 in
/-- End-to-end causal rolled route for the prime-row producer.  The mark and
normalize programs are audited at their honest source bounds, while their
ordinary executions are array-padded solely so the compiler relation retains
the caller-owned witness planes.  Each next stage starts from the preceding
stage's final physical memory.  Thus the conclusion contains neither a
trusted prime mask nor a trusted `PrimeRowsCorrect` premise.

The theorem is uniform in the segment and Goldbach row counts.  Its premises
are static schedule/readiness facts plus signature-shaped physical runs; it
does not execute either production fold in Lean. -/
theorem primeRowsCorrect_and_cells_of_rolled_segmented_pipeline
    (c : Cfg) (bootBound valid delta : Nat)
    (hSchedule :
      LeanCompCert.Ports.ArraySegMobiusIndexedFull.SingleMixedPaddedRootSchedule
        c.sieve bootBound valid delta)
    (hBaseEq : (1 + ((c.sieve.segLen + delta) % M)) % M = c.sieve.lo)
    (hTableLen :
      (LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed.rootScanMixed
        c.sieve.bootPrimes bootBound 1 valid).length = c.sieve.tableLen)
    (hBudget :
      ((LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed.rootScanMixed
        c.sieve.bootPrimes bootBound 1 valid).map
          fun p => c.sieve.segLen / p + 2).sum ≤ c.sieve.markSteps)
    (hIdxM : c.sieve.rootSpan + c.sieve.markSteps < M)
    (hRootSqM : c.sieve.rootCap * c.sieve.rootCap < M)
    (hSegRootM : c.sieve.segLen + c.sieve.rootCap < M)
    (hLoSegM : c.sieve.lo + c.sieve.segLen < M)
    (hAboveRoot : c.sieve.rootCap < c.sieve.lo)
    (hCovered : c.sieve.lo + c.sieve.segLen - 1 ≤
      c.sieve.rootCap * c.sieve.rootCap)
    (hSegPos : 0 < c.sieve.segLen) (hArrayM : c.arrayLen < M)
    (initial : Nat → Nat)
    (hZeroPrefix : ∀ j, j < c.sieve.arrayLen → initial j = 0)
    (hInitialWords : ∀ j, initial j < M)
    (base : Int) (hBase : BaseOk c.arrayLen base)
    (mem : Mem)
    (hCells : ∀ k, k < c.arrayLen →
      mem (cellAddr base k) = some (((initial k : Nat) : Int)))
    (hMarkAudit : TGEvenGoldbach.AuditRolledZero
      (RS62SegmentedPrimeMask.program c.sieve) base mem)
    (markedM : MCCState)
    (hMarkEval : evalMCCSequence
      (AProgram.initialMCCWithMem
        (AProgram.counterAugment (AProgram.padArray
          (RS62SegmentedPrimeMask.program c.sieve) c.arrayLen)) base mem)
      (AProgram.rolledCompile (AProgram.padArray
        (RS62SegmentedPrimeMask.program c.sieve) c.arrayLen)) = some markedM)
    (hNormalizeAudit : TGEvenGoldbach.AuditRolledZero
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) base
        markedM.mem)
    (normalizedM : MCCState)
    (hNormalizeEval : evalMCCSequence
      (AProgram.initialMCCWithMem
        (AProgram.counterAugment (AProgram.padArray
          (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen)
          c.arrayLen)) base markedM.mem)
      (AProgram.rolledCompile (AProgram.padArray
        (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) c.arrayLen)) =
          some normalizedM)
    (hPackAudit : TGEvenGoldbach.AuditRolledZero (program c) base
      normalizedM.mem)
    (packedM : MCCState)
    (hPackEval : evalMCCSequence
      ((program c).counterAugment.initialMCCWithMem base normalizedM.mem)
        (program c).rolledCompile = some packedM)
    (hPackZero : packedM.env ⟨(program c).output + 1⟩ = some (0 : Int)) :
    ∃ marked normalized packed,
      (RS62SegmentedPrimeMask.program c.sieve).runFromArray initial =
          some marked ∧
        (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).runFromArray
            marked.arr = some normalized ∧
        (program c).runFromArray normalized.arr = some packed ∧
        TGEvenGoldbach.PrimeRowsCorrect c.goldbach
          (outputArray c packed.arr) ∧
        (∀ k, k < c.goldbach.arrayLen →
          packedM.mem (cellAddr (scannerBase c base) k) =
            some ((((outputArray c packed.arr k) : Nat) : Int))) := by
  have hScratch : c.sieve.segLen ≤ c.sieve.arrayLen := by
    simp [LeanCompCert.Ports.ArraySegSieve.Cfg.arrayLen,
      LeanCompCert.Ports.ArraySegSieve.Cfg.resultBase]
    omega
  have hMarkPrefix :
      (RS62SegmentedPrimeMask.program c.sieve).arrayLen ≤ c.arrayLen := by
    simp only [RS62SegmentedPrimeMask.program, Cfg.arrayLen, Cfg.outputBase]
    omega
  have hMarkLen : 0 < (RS62SegmentedPrimeMask.program c.sieve).arrayLen := by
    simp only [RS62SegmentedPrimeMask.program]
    exact Nat.lt_of_lt_of_le hSegPos hScratch
  obtain ⟨marked, hMark, hMarkedCells⟩ :=
    source_run_and_full_cells_of_audit_padded_rolled
      (RS62SegmentedPrimeMask.program c.sieve)
      (RS62SegmentedPrimeMask.program_wf c.sieve) c.arrayLen hMarkPrefix
      hMarkLen hArrayM initial hInitialWords base hBase mem hCells hMarkAudit
      markedM hMarkEval
  have hMarkedWords : ∀ j, marked.arr j < M :=
    (LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (RS62SegmentedPrimeMask.program c.sieve) initial hInitialWords marked
      hMark).2
  have hNormalizePrefix :
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).arrayLen ≤
        c.arrayLen := by
    simp only [RS62SegmentedPrimeMask.normalizeProgram, Cfg.arrayLen,
      Cfg.outputBase]
    omega
  have hNormalizeLen :
      0 < (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).arrayLen := by
    simpa [RS62SegmentedPrimeMask.normalizeProgram] using hSegPos
  obtain ⟨normalized, hNormalize, hNormalizedCells⟩ :=
    source_run_and_full_cells_of_audit_padded_rolled
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen)
      (RS62SegmentedPrimeMask.normalizeProgram_wf c.sieve.segLen) c.arrayLen
      hNormalizePrefix hNormalizeLen hArrayM marked.arr hMarkedWords base
      hBase markedM.mem hMarkedCells hNormalizeAudit normalizedM
      hNormalizeEval
  have hNormalizedWords : ∀ j, normalized.arr j < M :=
    (LeanCompCert.Verified.ArrayAudit.AProgram.runFromArray_word
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) marked.arr
      hMarkedWords normalized hNormalize).2
  have hMask := maskCorrect_of_segmented_source_runs c bootBound valid delta
    hSchedule hBaseEq hTableLen hBudget hIdxM hRootSqM hSegRootM hLoSegM
    hAboveRoot hCovered initial marked normalized hZeroPrefix hMark hNormalize
  have hReady : Ready c normalized.arr :=
    ⟨hSegPos, hLoSegM, hArrayM, fun j _ => hNormalizedWords j⟩
  obtain ⟨packed, hPack, hPrimeRows, hPackedCells⟩ :=
    primeRowsCorrect_and_cells_of_rolled_state c normalized.arr hReady hMask
      base hBase normalizedM.mem hNormalizedCells hNormalizedWords hPackAudit
      packedM hPackEval hPackZero
  exact ⟨marked, normalized, packed, hMark, hNormalize, hPack, hPrimeRows,
    hPackedCells⟩

/-- Reusable manifest-facing package for the three causal producer stages.
It contains only static facts, represented input memory, and the audit/normal
rolled executions.  In particular, neither the mathematical mask nor
`PrimeRowsCorrect` is a field. -/
structure RolledSegmentedPipeline (c : Cfg) where
  bootBound : Nat
  valid : Nat
  delta : Nat
  schedule :
    LeanCompCert.Ports.ArraySegMobiusIndexedFull.SingleMixedPaddedRootSchedule
      c.sieve bootBound valid delta
  base_eq : (1 + ((c.sieve.segLen + delta) % M)) % M = c.sieve.lo
  table_len :
    (LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed.rootScanMixed
      c.sieve.bootPrimes bootBound 1 valid).length = c.sieve.tableLen
  budget :
    ((LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed.rootScanMixed
      c.sieve.bootPrimes bootBound 1 valid).map
        fun p => c.sieve.segLen / p + 2).sum ≤ c.sieve.markSteps
  idx_word : c.sieve.rootSpan + c.sieve.markSteps < M
  root_square_word : c.sieve.rootCap * c.sieve.rootCap < M
  segment_root_word : c.sieve.segLen + c.sieve.rootCap < M
  upper_word : c.sieve.lo + c.sieve.segLen < M
  above_root : c.sieve.rootCap < c.sieve.lo
  covered : c.sieve.lo + c.sieve.segLen - 1 ≤
    c.sieve.rootCap * c.sieve.rootCap
  segment_pos : 0 < c.sieve.segLen
  array_word : c.arrayLen < M
  initial : Nat → Nat
  zero_prefix : ∀ j, j < c.sieve.arrayLen → initial j = 0
  initial_words : ∀ j, initial j < M
  base : Int
  base_ok : BaseOk c.arrayLen base
  mem : Mem
  cells : ∀ k, k < c.arrayLen →
    mem (cellAddr base k) = some (((initial k : Nat) : Int))
  mark_audit : TGEvenGoldbach.AuditRolledZero
    (RS62SegmentedPrimeMask.program c.sieve) base mem
  marked : MCCState
  mark_eval : evalMCCSequence
    (AProgram.initialMCCWithMem
      (AProgram.counterAugment (AProgram.padArray
        (RS62SegmentedPrimeMask.program c.sieve) c.arrayLen)) base mem)
    (AProgram.rolledCompile (AProgram.padArray
      (RS62SegmentedPrimeMask.program c.sieve) c.arrayLen)) = some marked
  normalize_audit : TGEvenGoldbach.AuditRolledZero
    (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) base marked.mem
  normalized : MCCState
  normalize_eval : evalMCCSequence
    (AProgram.initialMCCWithMem
      (AProgram.counterAugment (AProgram.padArray
        (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) c.arrayLen))
      base marked.mem)
    (AProgram.rolledCompile (AProgram.padArray
      (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen) c.arrayLen)) =
        some normalized
  pack_audit : TGEvenGoldbach.AuditRolledZero (program c) base normalized.mem
  packed : MCCState
  pack_eval : evalMCCSequence
    ((program c).counterAugment.initialMCCWithMem base normalized.mem)
      (program c).rolledCompile = some packed
  pack_zero : packed.env ⟨(program c).output + 1⟩ = some (0 : Int)

/-- Exact denotation exposed by the reusable causal package. -/
theorem RolledSegmentedPipeline.sound {c : Cfg}
    (r : RolledSegmentedPipeline c) :
    ∃ marked normalized packed,
      (RS62SegmentedPrimeMask.program c.sieve).runFromArray r.initial =
          some marked ∧
        (RS62SegmentedPrimeMask.normalizeProgram c.sieve.segLen).runFromArray
            marked.arr = some normalized ∧
        (program c).runFromArray normalized.arr = some packed ∧
        TGEvenGoldbach.PrimeRowsCorrect c.goldbach
          (outputArray c packed.arr) ∧
        (∀ k, k < c.goldbach.arrayLen →
          r.packed.mem (cellAddr (scannerBase c r.base) k) =
            some ((((outputArray c packed.arr k) : Nat) : Int))) := by
  exact primeRowsCorrect_and_cells_of_rolled_segmented_pipeline c r.bootBound
    r.valid r.delta r.schedule r.base_eq r.table_len r.budget r.idx_word
    r.root_square_word r.segment_root_word r.upper_word r.above_root r.covered
    r.segment_pos r.array_word r.initial r.zero_prefix r.initial_words r.base
    r.base_ok r.mem r.cells r.mark_audit r.marked r.mark_eval r.normalize_audit
    r.normalized r.normalize_eval r.pack_audit r.packed r.pack_eval r.pack_zero

/-- Package a retained producer state as the existing literal Goldbach
receipt.  The downstream audit/run signatures start from the producer's final
memory, so this is a causal continuation rather than two unrelated receipts. -/
def goldbachReceipt_of_retained_primeRows
    (c : Cfg) (arr : Nat → Nat) (out : AState)
    (hready : Ready c arr) (harr : ∀ k, arr k < M)
    (hRun : (program c).runFromArray arr = some out)
    (hprime : TGEvenGoldbach.PrimeRowsCorrect c.goldbach
      (outputArray c out.arr))
    (base : Int) (hBase : BaseOk c.arrayLen base)
    (m : LeanCompCert.Verified.MemFragment.MCCState)
    (hPhysicalCells : ∀ k, k < c.goldbach.arrayLen →
      m.mem (cellAddr (scannerBase c base) k) =
        some ((((outputArray c out.arr k) : Nat) : Int)))
    (hcount : 0 < c.goldbach.count)
    (hEvenRoom : c.goldbach.evenLo + 2 * c.goldbach.count < M)
    (hGoldAudit : TGEvenGoldbach.AuditRolledZero
      (TGEvenGoldbach.program c.goldbach) (scannerBase c base) m.mem)
    (hGoldRun : TGEvenGoldbach.RolledResult
      (TGEvenGoldbach.program c.goldbach) (scannerBase c base) m.mem 0) :
    TGEvenGoldbach.RolledReceipt c.goldbach (outputArray c out.arr) := by
  have houtWords := run_words_all c arr out hready harr hRun
  have hGoldLen : c.goldbach.arrayLen < M := by
    have htotal := hready.2.2.1
    simp only [Cfg.arrayLen] at htotal
    omega
  have hGoldReady : TGEvenGoldbach.Ready c.goldbach
      (outputArray c out.arr) := by
    refine ⟨hGoldLen, hEvenRoom, ?_⟩
    intro i _hi
    unfold outputArray
    exact houtWords (c.outputBase + i)
  refine {
    count_pos := hcount
    ready := hGoldReady
    primeRows := hprime
    base := scannerBase c base
    baseOk := scannerBase_ok c base hBase
    mem := m.mem
    cells := hPhysicalCells
    words := ?_
    audit := hGoldAudit
    run := hGoldRun }
  intro i
  unfold outputArray
  exact houtWords (c.outputBase + i)

#print axioms body_arr_of_ne
#print axioms source_run_and_full_cells_of_audit_padded_rolled
#print axioms packedState_inv
#print axioms primes_of_rowAccepted
#print axioms primeRowsCorrect_of_packed_zero
#print axioms primeRowsCorrect_of_run_zero
#print axioms maskCorrect_of_segmented_source_runs
#print axioms primeRowsCorrect_of_segmented_source_pipeline
#print axioms primeRowsCorrect_of_rolled_acceptance
#print axioms scannerBase_ok
#print axioms primeRowsCorrect_and_cells_of_rolled_state
#print axioms primeRowsCorrect_and_cells_of_rolled_segmented_pipeline
#print axioms RolledSegmentedPipeline.sound

end LeanCompCert.Ports.TGEvenGoldbachPrimeRows

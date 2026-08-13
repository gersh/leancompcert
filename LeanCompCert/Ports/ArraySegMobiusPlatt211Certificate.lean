import LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest
import LeanCompCert.Ports.ArraySegMobiusSignal
import LeanCompCert.Ports.ArraySegMobiusExtrema
import LeanCompCert.Verified.ArrayAudit

/-!
# Compiled observation contract for the Platt (2.11) manifest

This file gives the completed 1,092-window campaign one exact LeanCompCert
run boundary.  Each row reconstructs the literal source configuration, seed,
and historical threshold and observes the returned violation count plus the
three stored extrema cells.  A second admission records the completed
fail-safe audit of the same reconstructed program.

The admissions are finite physical-run facts.  They do not assert the paper
theorem: source definedness, segmented-sieve refinement, carry composition,
and the paper-side strict thresholds remain theorem layers.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlatt211Certificate

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayComputation
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.MemFragment
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusPlatt211ManifestData
open LeanCompCert.Ports.ArraySegMobiusPlatt211Manifest

theorem artifactProgram_arrayLen (row : Row) :
    (artifactProgram row).arrayLen =
      3 * row.segLen + row.mainCount + 18 := rfl

theorem rowCfg_arrayLen_lt (row : Row) (hrow : row ∈ rows) :
    (artifactProgram row).arrayLen < M := by
  have hbool := (List.all_eq_true.mp cfgShapes_ok) row hrow
  unfold cfgShapeOK at hbool
  have hshape := of_decide_eq_true hbool
  rcases hshape with ⟨_, _, _, _, _, _, hbytes⟩
  rw [artifactProgram_arrayLen]
  have hM : 0 < M := M_pos
  omega

theorem rowCfg_baseOk (row : Row) (hrow : row ∈ rows) :
    BaseOk (artifactProgram row).arrayLen 0 := by
  have hbool := (List.all_eq_true.mp cfgShapes_ok) row hrow
  unfold cfgShapeOK at hbool
  have hshape := of_decide_eq_true hbool
  rcases hshape with ⟨_, _, _, _, _, _, hbytes⟩
  have hlen := artifactProgram_arrayLen row
  have hbytes' : 8 * (artifactProgram row).arrayLen ≤ M := by
    rw [hlen]
    exact hbytes
  unfold BaseOk
  constructor
  · omega
  · apply Int.ofNat_le.mpr
    simpa using hbytes'

/-- Closed reconstructed computation for one manifest row. -/
def rowComputation (row : Row) (hrow : row ∈ rows) : AComputation where
  program := artifactProgram row
  wellFormed := mobiusProgram_wf (rowCfg row) row.seed row.threshold
  base := 0
  baseOk := rowCfg_baseOk row hrow
  name := s!"platt211-window-{row.idx}"

/-- The exact output local and three result cells observed by the production
driver. -/
def rowObservation (row : Row) (hrow : row ∈ rows) : Option (Int × List Int) := do
  let a := rowComputation row hrow
  let m ← evalMCCSequence (a.program.initialMCC a.base) a.program.compile
  let result ← m.env ⟨a.program.output + 1⟩
  let cells ← (List.range 3).mapM fun slot =>
    m.mem (cellAddr a.base ((rowCfg row).resultBase + slot))
  pure (result, cells)

def rowExpectedObservation (row : Row) : Option (Int × List Int) :=
  some (row.violations, [row.tOut, row.tMax, row.tMin])

/-- CompCert 3.17 reproduced every retained output local and extrema cell for
the reconstructed 1,092-window campaign. -/
axiom platt211_compcert_run (row : Row) (hrow : row ∈ rows) :
  rowObservation row hrow = rowExpectedObservation row

/-- The mechanically guarded version of every reconstructed row returned
zero failed division/address guards in the completed audit campaign. -/
axiom platt211Audit_compcert_run (row : Row) (hrow : row ∈ rows) :
  (auditComputation (rowComputation row hrow)).Returns ((0 : Nat) : Int)

/-- The aggregate observation contains the ordinary output receipt used by
the honest array-run rule. -/
theorem row_returns (row : Row) (hrow : row ∈ rows) :
    (rowComputation row hrow).Returns (row.violations : Int) := by
  have h := platt211_compcert_run row hrow
  cases hm : evalMCCSequence
      ((rowComputation row hrow).program.initialMCC
        (rowComputation row hrow).base)
      (rowComputation row hrow).program.compile with
  | none =>
      simp [rowObservation, rowExpectedObservation, hm] at h
  | some m =>
      cases hr : m.env ⟨(rowComputation row hrow).program.output + 1⟩ with
      | none =>
          simp [rowObservation, rowExpectedObservation, hm, hr] at h
      | some result =>
          cases hc : (List.range 3).mapM fun slot =>
              m.mem (cellAddr (rowComputation row hrow).base
                ((rowCfg row).resultBase + slot)) with
          | none =>
              simp [rowObservation, rowExpectedObservation, hm, hr, hc] at h
          | some cells =>
              simp [rowObservation, rowExpectedObservation, hm, hr, hc] at h
              have hresult : result = (row.violations : Int) := by
                exact h.1
              unfold AComputation.Returns AComputation.sourceResult
              simp only [hm, Option.bind_some, hr, hresult]

/-- The aggregate physical receipt exposes each of the three final result
cells individually.  These are observations of the identical compiled trace,
not three additional runs. -/
theorem row_observes_resultCells (row : Row) (hrow : row ∈ rows) :
    (rowComputation row hrow).ObservesCell ((rowCfg row).resultBase + 0)
        (row.tOut : Int) ∧
      (rowComputation row hrow).ObservesCell ((rowCfg row).resultBase + 1)
        (row.tMax : Int) ∧
      (rowComputation row hrow).ObservesCell ((rowCfg row).resultBase + 2)
        (row.tMin : Int) := by
  have h := platt211_compcert_run row hrow
  cases hm : evalMCCSequence
      ((rowComputation row hrow).program.initialMCC
        (rowComputation row hrow).base)
      (rowComputation row hrow).program.compile with
  | none =>
      simp [rowObservation, rowExpectedObservation, hm] at h
  | some m =>
      cases hr : m.env ⟨(rowComputation row hrow).program.output + 1⟩ with
      | none =>
          simp [rowObservation, rowExpectedObservation, hm, hr] at h
      | some result =>
          cases hc : (List.range 3).mapM fun slot =>
              m.mem (cellAddr (rowComputation row hrow).base
                ((rowCfg row).resultBase + slot)) with
          | none =>
              simp [rowObservation, rowExpectedObservation, hm, hr, hc] at h
          | some cells =>
              have hpair : (result, cells) =
                  ((row.violations : Int),
                    [(row.tOut : Int), (row.tMax : Int), (row.tMin : Int)]) := by
                simpa [rowObservation, rowExpectedObservation, hm, hr, hc]
                  using h
              have hcells : cells =
                  [(row.tOut : Int), (row.tMax : Int), (row.tMin : Int)] := by
                simpa using congrArg Prod.snd hpair
              rw [hcells] at hc
              change ([0, 1, 2] : List Nat).mapM (fun slot =>
                  m.mem (cellAddr (rowComputation row hrow).base
                    ((rowCfg row).resultBase + slot))) =
                some [(row.tOut : Int), (row.tMax : Int), (row.tMin : Int)] at hc
              cases h0 : m.mem (cellAddr (rowComputation row hrow).base
                  (rowCfg row).resultBase) with
              | none => simp [h0] at hc
              | some v0 =>
                  cases h1 : m.mem (cellAddr (rowComputation row hrow).base
                      ((rowCfg row).resultBase + 1)) with
                  | none => simp [h0, h1] at hc
                  | some v1 =>
                      cases h2 : m.mem (cellAddr (rowComputation row hrow).base
                          ((rowCfg row).resultBase + 2)) with
                      | none => simp [h0, h1, h2] at hc
                      | some v2 =>
                          simp [h0, h1, h2] at hc
                          rcases hc with ⟨hv0, hv1, hv2⟩
                          unfold AComputation.ObservesCell
                          simp only [hm, Option.bind_some]
                          exact ⟨by simpa [hv0] using h0,
                            by simpa [hv1] using h1,
                            by simpa [hv2] using h2⟩

/-- The completed fail-safe receipt establishes source definedness, after
which the ordinary output receipt identifies the exact violation count. -/
theorem row_denote (row : Row) (hrow : row ∈ rows) :
    (rowComputation row hrow).program.denote = some row.violations := by
  obtain ⟨n, hn⟩ := source_denotes_of_audit_returns_zero
    (rowComputation row hrow) (by
      change 0 < (artifactProgram row).arrayLen
      rw [artifactProgram_arrayLen]
      omega) (rowCfg_arrayLen_lt row hrow)
    (platt211Audit_compcert_run row hrow)
  have hv : row.violations = n :=
    AComputation.value_of_returns (rowComputation row hrow) hn
      (row_returns row hrow)
  simpa only [← hv] using hn

/-- The three observed result words are the three source extrema registers at
the end of the manifest row.  The audit receipt first establishes source
definedness; the final-memory compiler relation then transports the observed
cells back to the ordinary source trace. -/
theorem row_source_final_resultCells (row : Row) (hrow : row ∈ rows) :
    let a := rowComputation row hrow
    let sEntry := arun 0 initialAState a.program.init
    let sLoop := (List.range a.program.loopCount).foldl
      (fun s idx => arun idx s a.program.body) sEntry
    let sFinal := arun 0 sLoop a.program.epilogue
    sFinal.arr ((rowCfg row).resultBase + 0) = row.tOut ∧
      sFinal.arr ((rowCfg row).resultBase + 1) = row.tMax ∧
      sFinal.arr ((rowCfg row).resultBase + 2) = row.tMin := by
  have hobs := row_observes_resultCells row hrow
  let a := rowComputation row hrow
  have hlen : 0 < a.program.arrayLen := by
    change 0 < (artifactProgram row).arrayLen
    rw [artifactProgram_arrayLen]
    omega
  have hcell0 : (rowCfg row).resultBase + 0 < a.program.arrayLen := by
    simp [a, rowComputation, artifactProgram, mobiusProgram, Cfg.program,
      Cfg.arrayLen, Cfg.resultBase]
  have hcell1 : (rowCfg row).resultBase + 1 < a.program.arrayLen := by
    simp [a, rowComputation, artifactProgram, mobiusProgram, Cfg.program,
      Cfg.arrayLen, Cfg.resultBase]
  have hcell2 : (rowCfg row).resultBase + 2 < a.program.arrayLen := by
    simp [a, rowComputation, artifactProgram, mobiusProgram, Cfg.program,
      Cfg.arrayLen, Cfg.resultBase]
  exact ⟨source_total_cell_eq_of_audit_and_observesCell a
      ((rowCfg row).resultBase + 0) hcell0 row.tOut hlen
      (rowCfg_arrayLen_lt row hrow) (platt211Audit_compcert_run row hrow)
      hobs.1,
    source_total_cell_eq_of_audit_and_observesCell a
      ((rowCfg row).resultBase + 1) hcell1 row.tMax hlen
      (rowCfg_arrayLen_lt row hrow) (platt211Audit_compcert_run row hrow)
      hobs.2.1,
    source_total_cell_eq_of_audit_and_observesCell a
      ((rowCfg row).resultBase + 2) hcell2 row.tMin hlen
      (rowCfg_arrayLen_lt row hrow) (platt211Audit_compcert_run row hrow)
      hobs.2.2⟩

private theorem arun_storeResult_arr_self (c : Cfg) (slot reg k : Nat)
    (s : AState) (haddr : c.resultBase + slot < M) (hreg : reg ≠ 90) :
    (arun k s (storeResult c slot reg)).arr (c.resultBase + slot) =
      s.regs reg := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, haddr, hreg,
    Nat.mod_eq_of_lt]

private theorem arun_storeResult_arr_ne (c : Cfg) (slot reg cell k : Nat)
    (s : AState) (haddr : c.resultBase + slot < M)
    (hne : cell ≠ c.resultBase + slot) :
    (arun k s (storeResult c slot reg)).arr cell = s.arr cell := by
  simp [storeResult, arun, astep, AState.writeReg, AState.writeArr,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, denoteOperand, haddr, hne,
    Nat.mod_eq_of_lt]

private theorem arun_storeResult_reg_frame (c : Cfg) (slot reg keep k : Nat)
    (s : AState) (hkeep : keep ≠ 90) :
    (arun k s (storeResult c slot reg)).regs keep = s.regs keep := by
  simp [storeResult, arun, astep, AState.writeReg,
    AState.writeArr_regs,
    LeanCompCert.Verified.InstrBlock.sdest,
    LeanCompCert.Verified.InstrBlock.sval, hkeep]

private theorem arun_mobiusEpilogue_resultCells (c : Cfg) (thr : Nat)
    (s : AState) (hM : c.resultBase + 9 < M) :
    let out := arun 0 s (mobiusEpilogue c thr)
    out.arr (c.resultBase + 0) = s.regs rT ∧
      out.arr (c.resultBase + 1) = s.regs rTmax ∧
      out.arr (c.resultBase + 2) = s.regs rTmin := by
  let tested := arun 0 (arun 0 s (gtTest rVTHi rTmax (tBias + thr)))
    (ltTest rVTLo rTmin (tBias - thr))
  let s0 := arun 0 tested (storeResult c 0 rT)
  let s1 := arun 0 s0 (storeResult c 1 rTmax)
  let s2 := arun 0 s1 (storeResult c 2 rTmin)
  let s8 := arun 0 s2 (storeResult c 8 rVTHi)
  let s9 := arun 0 s8 (storeResult c 9 rVTLo)
  have hout : arun 0 s (mobiusEpilogue c thr) = s9 := by
    simp [mobiusEpilogue, storeResults, mobiusViolRegs, arun_append,
      tested, s0, s1, s2, s8, s9]
  have htestedT : tested.regs rT = s.regs rT := by
    dsimp only [tested]
    rw [LeanCompCert.Ports.ArraySegMobiusSignal.arun_reg_frame]
    · rw [LeanCompCert.Ports.ArraySegMobiusSignal.arun_reg_frame]
      rfl
    · rfl
  have htestedMax : tested.regs rTmax = s.regs rTmax := by
    dsimp only [tested]
    rw [LeanCompCert.Ports.ArraySegMobiusSignal.arun_reg_frame]
    · rw [LeanCompCert.Ports.ArraySegMobiusSignal.arun_reg_frame]
      rfl
    · rfl
  have htestedMin : tested.regs rTmin = s.regs rTmin := by
    dsimp only [tested]
    rw [LeanCompCert.Ports.ArraySegMobiusSignal.arun_reg_frame]
    · rw [LeanCompCert.Ports.ArraySegMobiusSignal.arun_reg_frame]
      rfl
    · rfl
  have h0M : c.resultBase + 0 < M := by omega
  have h1M : c.resultBase + 1 < M := by omega
  have h2M : c.resultBase + 2 < M := by omega
  have h8M : c.resultBase + 8 < M := by omega
  have h0 : s9.arr (c.resultBase + 0) = s.regs rT := by
    calc
      _ = s8.arr (c.resultBase + 0) :=
        arun_storeResult_arr_ne c 9 rVTLo _ 0 s8 (by omega) (by omega)
      _ = s2.arr (c.resultBase + 0) :=
        arun_storeResult_arr_ne c 8 rVTHi _ 0 s2 h8M (by omega)
      _ = s1.arr (c.resultBase + 0) :=
        arun_storeResult_arr_ne c 2 rTmin _ 0 s1 h2M (by omega)
      _ = s0.arr (c.resultBase + 0) :=
        arun_storeResult_arr_ne c 1 rTmax _ 0 s0 h1M (by omega)
      _ = tested.regs rT :=
        arun_storeResult_arr_self c 0 rT 0 tested h0M (by decide)
      _ = s.regs rT := htestedT
  have h1 : s9.arr (c.resultBase + 1) = s.regs rTmax := by
    calc
      _ = s8.arr (c.resultBase + 1) :=
        arun_storeResult_arr_ne c 9 rVTLo _ 0 s8 (by omega) (by omega)
      _ = s2.arr (c.resultBase + 1) :=
        arun_storeResult_arr_ne c 8 rVTHi _ 0 s2 h8M (by omega)
      _ = s1.arr (c.resultBase + 1) :=
        arun_storeResult_arr_ne c 2 rTmin _ 0 s1 h2M (by omega)
      _ = s0.regs rTmax :=
        arun_storeResult_arr_self c 1 rTmax 0 s0 h1M (by decide)
      _ = tested.regs rTmax :=
        arun_storeResult_reg_frame c 0 rT rTmax 0 tested (by decide)
      _ = s.regs rTmax := htestedMax
  have h2 : s9.arr (c.resultBase + 2) = s.regs rTmin := by
    calc
      _ = s8.arr (c.resultBase + 2) :=
        arun_storeResult_arr_ne c 9 rVTLo _ 0 s8 (by omega) (by omega)
      _ = s2.arr (c.resultBase + 2) :=
        arun_storeResult_arr_ne c 8 rVTHi _ 0 s2 h8M (by omega)
      _ = s1.regs rTmin :=
        arun_storeResult_arr_self c 2 rTmin 0 s1 h2M (by decide)
      _ = s0.regs rTmin :=
        arun_storeResult_reg_frame c 1 rTmax rTmin 0 s0 (by decide)
      _ = tested.regs rTmin :=
        arun_storeResult_reg_frame c 0 rT rTmin 0 tested (by decide)
      _ = s.regs rTmin := htestedMin
  rw [hout]
  exact ⟨h0, h1, h2⟩

/-- The physical result-cell receipt identifies the three persistent extrema
registers at loop exit, before the observation-only epilogue runs. -/
theorem row_source_loop_extrema (row : Row) (hrow : row ∈ rows) :
    let a := rowComputation row hrow
    let sEntry := arun 0 initialAState a.program.init
    let sLoop := (List.range a.program.loopCount).foldl
      (fun s idx => arun idx s a.program.body) sEntry
    ArraySegMobiusExtrema.readExt sLoop =
      ⟨row.tOut, row.tMax, row.tMin⟩ := by
  let a := rowComputation row hrow
  let sEntry := arun 0 initialAState a.program.init
  let sLoop := (List.range a.program.loopCount).foldl
    (fun s idx => arun idx s a.program.body) sEntry
  have hfinal := row_source_final_resultCells row hrow
  change
    (arun 0 sLoop a.program.epilogue).arr ((rowCfg row).resultBase + 0) =
        row.tOut ∧
      (arun 0 sLoop a.program.epilogue).arr ((rowCfg row).resultBase + 1) =
        row.tMax ∧
      (arun 0 sLoop a.program.epilogue).arr ((rowCfg row).resultBase + 2) =
        row.tMin at hfinal
  have hM : (rowCfg row).resultBase + 9 < M := by
    exact Nat.lt_trans
      (by simp [artifactProgram, mobiusProgram, Cfg.program, Cfg.arrayLen] :
        (rowCfg row).resultBase + 9 < (artifactProgram row).arrayLen)
      (rowCfg_arrayLen_lt row hrow)
  have hepi := arun_mobiusEpilogue_resultCells
    (rowCfg row) row.threshold sLoop hM
  change
    (arun 0 sLoop (mobiusEpilogue (rowCfg row) row.threshold)).arr
          ((rowCfg row).resultBase + 0) = sLoop.regs rT ∧
      (arun 0 sLoop (mobiusEpilogue (rowCfg row) row.threshold)).arr
          ((rowCfg row).resultBase + 1) = sLoop.regs rTmax ∧
      (arun 0 sLoop (mobiusEpilogue (rowCfg row) row.threshold)).arr
          ((rowCfg row).resultBase + 2) = sLoop.regs rTmin at hepi
  have hepilogue : a.program.epilogue =
      mobiusEpilogue (rowCfg row) row.threshold := rfl
  rw [hepilogue] at hfinal
  change MobiusExtremaScalar.Ext.mk (sLoop.regs rT)
      (sLoop.regs rTmax) (sLoop.regs rTmin) =
    MobiusExtremaScalar.Ext.mk row.tOut row.tMax row.tMin
  rw [hepi.1.symm.trans hfinal.1,
    hepi.2.1.symm.trans hfinal.2.1,
    hepi.2.2.symm.trans hfinal.2.2]

/-- The loop identified by the physical receipt is definitionally the
changing-index combined sieve/extrema runner used by the refinement layer. -/
theorem row_combined_loop_extrema (row : Row) (hrow : row ∈ rows) :
    let c := rowCfg row
    let entry := arun 0 initialAState (c.coreInit ++ mobiusInit row.seed)
    ArraySegMobiusExtrema.readExt
        (ArraySegMobiusExtrema.combinedIndexedRun 0 c
          (c.period * (c.rootCount + c.segCount)) entry) =
      ⟨row.tOut, row.tMax, row.tMin⟩ := by
  have h := row_source_loop_extrema row hrow
  let c := rowCfg row
  let entry := arun 0 initialAState (c.coreInit ++ mobiusInit row.seed)
  change ArraySegMobiusExtrema.readExt
      ((List.range (c.period * (c.rootCount + c.segCount))).foldl
        (fun s idx => arun idx s (c.coreBody ++ mobiusOverNResidue)) entry) =
    ⟨row.tOut, row.tMax, row.tMin⟩ at h
  have heq := ArraySegMobiusExtrema.foldl_range_combined_eq_combinedIndexedRun
    0 c (c.period * (c.rootCount + c.segCount)) entry
  simp only [Nat.zero_add] at heq
  rw [heq] at h
  exact h

/-- A successful denotation of the historical extrema residue rules out its
only dynamic failure mode: division by a zero candidate. -/
private theorem candidate_ne_zero_of_residue_denotes
    (len idx : Nat) (s out : AState)
    (h : denoteAInstrs len idx s mobiusOverNResidue = some out) :
    s.regs 65 ≠ 0 := by
  intro hz
  simp [mobiusOverNResidue, denoteAInstrs, denoteAInstr, denoteInstr,
    denoteOperand, denoteOp, hz] at h

/-- The compiled fail-safe receipt supplies the nonzero candidate guard at
every loop prefix.  This extracts the guard from source definedness instead
of asking the kernel to replay the production candidate bounds. -/
theorem row_source_candidate_ready (row : Row) (hrow : row ∈ rows) :
    let c := rowCfg row
    let entry := arun 0 initialAState (c.coreInit ++ mobiusInit row.seed)
    ∀ j, j < c.period * (c.rootCount + c.segCount) →
      (arun j (ArraySegMobiusExtrema.combinedIndexedRun 0 c j entry)
        c.coreBody).regs 65 ≠ 0 := by
  dsimp only
  intro j hj
  let p := artifactProgram row
  have hbody : p.body =
      (rowCfg row).coreBody ++ mobiusOverNResidue := rfl
  have hinit : p.init =
      (rowCfg row).coreInit ++ mobiusInit row.seed := rfl
  have heq := ArraySegMobiusExtrema.foldl_range_combined_eq_combinedIndexedRun
    0 (rowCfg row) j
    (arun 0 initialAState
      ((rowCfg row).coreInit ++ mobiusInit row.seed))
  simp only [Nat.zero_add] at heq
  obtain ⟨coreOut, out, hcore, hres⟩ :=
    LeanCompCert.Verified.ArrayFoldBridge.AProgram.body_append_denotes_at_total_prefix
      p (row_denote row hrow) hj (rowCfg row).coreBody
        mobiusOverNResidue hbody
  have hcoreEq := eq_arun_of_denoteAInstrs_eq_some p.arrayLen j
    (rowCfg row).coreBody
    ((List.range j).foldl
      (fun s index => arun index s
        ((rowCfg row).coreBody ++ mobiusOverNResidue))
      (arun 0 initialAState p.init)) coreOut hcore
  rw [hinit, heq] at hcoreEq
  have hne := candidate_ne_zero_of_residue_denotes
    p.arrayLen j coreOut out hres
  rw [hcoreEq] at hne
  exact hne

#print axioms row_returns
#print axioms row_denote
#print axioms row_source_final_resultCells
#print axioms row_source_loop_extrema
#print axioms row_combined_loop_extrema
#print axioms row_source_candidate_ready

end LeanCompCert.Ports.ArraySegMobiusPlatt211Certificate

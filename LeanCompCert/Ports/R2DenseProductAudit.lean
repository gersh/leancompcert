import LeanCompCert.Ports.R2DenseProductAuditCore

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanCompCert.Ports.R2SegSieve.R2DenseProductAudit

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Verified.ArrayRegFrame
open LeanCompCert.Verified.ArrayAudit
open LeanCompCert.Ports.R2SegSieve.R2ProductAudit

theorem every_audited_product_fits_of_loop_zero
    (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat)
    (harr : ∀ i, arr i < M)
    (hloopZero : (auditedLoop c seed arr).regs auditReg = 0) :
    ∀ j, j < c.markSteps →
      (auditedBeforeMul c seed arr j).regs 35 *
        (auditedBeforeMul c seed arr j).regs rBp < M := by
  have hbody := denseSourceBody_wf c seed
  apply rangeFold_local_of_final_zero (sourceProgram c seed).body
    (auditedEntry c seed arr) c.markSteps auditReg
    (auditedEntry_word c seed arr harr) (denseAuditBody_mono c seed)
    (by rw [← auditedLoop_eq_rangeFold]; exact hloopZero)
    (fun j s => (arun j s (denseProductBeforeBody c)).regs 35 *
      (arun j s (denseProductBeforeBody c)).regs rBp < M)
  intro j s hs hs0 hsAfter
  have hzStep := hsAfter
  rw [sourceProgram_body] at hzStep
  exact product_fits_of_audited_dense_body_zero c j s
    (fun i hi => hbody i (List.mem_of_mem_drop hi)) hs hs0 hzStep

theorem original_product_fits_at_of_loop_zero
    (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat)
    (harr : ∀ i, arr i < M)
    (hloopZero : (auditedLoop c seed arr).regs auditReg = 0)
    (j : Nat) (hj : j < c.markSteps) :
    (originalBeforeMul c seed arr j).regs 35 *
      (originalBeforeMul c seed arr j).regs rBp < M := by
  have hfit := every_audited_product_fits_of_loop_zero
    c seed arr harr hloopZero j hj
  have hagree := auditedBeforeMul_sourceAgree c seed arr j
  rw [← hagree.2 35 (by decide), ← hagree.2 rBp (by decide)]
  exact hfit

theorem every_original_product_fits_of_loop_zero
    (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat)
    (harr : ∀ i, arr i < M)
    (hloopZero : (auditedLoop c seed arr).regs auditReg = 0) :
    ∀ j, j < c.markSteps →
      (originalBeforeMul c seed arr j).regs 35 *
        (originalBeforeMul c seed arr j).regs rBp < M :=
  fun j hj => original_product_fits_at_of_loop_zero c seed arr harr hloopZero j hj

theorem loop_zeros_of_source_run
    (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat)
    (harr : ∀ i, arr i < M) (out : AState)
    (hrun : (sourceProgram c seed).runFromArray arr = some out)
    (hout : out.regs auditReg = 0) :
    (auditedLoop c seed arr).regs auditReg = 0 ∧
      (auditedLoop c seed arr).regs rVMark = 0 := by
  have houtEq := AProgram.eq_arun_of_runFromArray_eq_some
    (sourceProgram c seed) arr out hrun
  have hfinal : (arun 0 (auditedLoop c seed arr) acceptBody).regs auditReg = 0 := by
    rw [houtEq] at hout
    simpa only [auditedLoop, auditedPrefix, auditedEntry,
      sourceProgram_loopCount, sourceProgram_epilogue] using hout
  have hloopWord : WordState (auditedLoop c seed arr) := by
    rw [auditedLoop_eq_rangeFold]
    exact fold_word _ _ _ (auditedEntry_word c seed arr harr)
  exact acceptBody_zero_sound _ hloopWord hfinal

theorem sourceRun_arr_eq_originalPrefix
    (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat) (out : AState)
    (hrun : (sourceProgram c seed).runFromArray arr = some out) :
    out.arr = (originalPrefix c seed arr c.markSteps).arr := by
  have houtEq := AProgram.eq_arun_of_runFromArray_eq_some
    (sourceProgram c seed) arr out hrun
  have haudit : out.arr = (auditedLoop c seed arr).arr := by
    rw [houtEq]
    simp only [auditedLoop, auditedPrefix, auditedEntry,
      sourceProgram_loopCount, sourceProgram_epilogue]
    exact LeanCompCert.Verified.ArrayScalarBlock.arun_scalarOnly_arr
      0 acceptBody (auditedLoop c seed arr) (by
        simp [acceptBody, LeanCompCert.Verified.ArrayScalarBlock.ScalarOnly])
  exact haudit.trans (auditedPrefix_sourceAgree c seed arr c.markSteps).1

theorem every_original_product_fits_and_vmark_zero_of_source_run
    (c : R2Cfg) (seed : R2Seed) (arr : Nat → Nat)
    (harr : ∀ i, arr i < M) (out : AState)
    (hrun : (sourceProgram c seed).runFromArray arr = some out)
    (hout : out.regs auditReg = 0) :
    (∀ j, j < c.markSteps →
      (originalBeforeMul c seed arr j).regs 35 *
        (originalBeforeMul c seed arr j).regs rBp < M) ∧
      (auditedLoop c seed arr).regs rVMark = 0 := by
  have hz := loop_zeros_of_source_run c seed arr harr out hrun hout
  exact ⟨every_original_product_fits_of_loop_zero c seed arr harr hz.1, hz.2⟩

#print axioms original_product_fits_at_of_loop_zero
#print axioms loop_zeros_of_source_run
#print axioms sourceRun_arr_eq_originalPrefix
#print axioms every_original_product_fits_and_vmark_zero_of_source_run

end LeanCompCert.Ports.R2SegSieve.R2DenseProductAudit

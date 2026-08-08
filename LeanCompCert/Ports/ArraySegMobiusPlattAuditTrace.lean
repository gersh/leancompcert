import LeanCompCert.Ports.ArraySegMobiusPlattAuditTraceGeneric

/-!
# Opaque trace composition for the aligned Platt receipts

This module is intentionally separate from the receipt declarations.  Each
rewrite crosses a small compiled theorem boundary, preventing elaboration from
unfolding a literal multi-billion-event configuration into the generic audit
proof term.
-/

namespace LeanCompCert.Ports.ArraySegMobiusPlattAuditTrace

open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.ArrayState
open LeanCompCert.Verified.ArrayFoldBridge
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusResidueFrame
open LeanCompCert.Ports.ArraySegMobiusSquaredFold
open LeanCompCert.Ports.MobiusResidueRealisation
open LeanCompCert.Ports.ArraySegMobiusPlattConfig
open LeanCompCert.Ports.ArraySegMobiusPlattAuditCertificate
open LeanCompCert.Ports.ArraySegMobiusPlattAuditTraceGeneric

/-- First link, kept in the exact syntactic form produced by the universal
trace theorem so checking this specialization needs no recursive reduction. -/
theorem plattFirst_indexed_viol_zero :
    let fuel := plattAlignedFirst.period *
      (plattAlignedFirst.rootCount + plattAlignedFirst.segCount)
    (squaredCombinedIndexedRun 0 plattAlignedFirst mobWideBits fuel
      (combinedEntry plattAlignedFirst plattFirstSeed)).regs
      rMViol = 0 := by
  exact squaredComputation_total_output_to_indexed_viol_zero
    plattFirstComputation plattAlignedFirst mobWideBits plattFirstSeed
    plattFirst_program
    plattFirst_total_output_zero

/-- Tail link in the same opaque trace form. -/
theorem plattTail_indexed_viol_zero :
    let fuel := plattAlignedTail.period *
      (plattAlignedTail.rootCount + plattAlignedTail.segCount)
    (squaredCombinedIndexedRun 0 plattAlignedTail mobWideBits fuel
      (combinedEntry plattAlignedTail plattTailSeed)).regs
      rMViol = 0 := by
  exact squaredComputation_total_output_to_indexed_viol_zero
    plattTailComputation plattAlignedTail mobWideBits plattTailSeed
    plattTail_program
    plattTail_total_output_zero

/-- The opening indexed trace exposes the exact low carry consumed by the
tail initializer. -/
theorem plattFirst_indexed_tLo :
    let fuel := plattAlignedFirst.period *
      (plattAlignedFirst.rootCount + plattAlignedFirst.segCount)
    (squaredCombinedIndexedRun 0 plattAlignedFirst mobWideBits fuel
      (combinedEntry plattAlignedFirst plattFirstSeed)).regs rTLo =
      1711921466838888838 := by
  exact squaredComputation_total_tLo_to_indexed
    plattFirstComputation plattAlignedFirst mobWideBits plattFirstSeed
    plattFirst_program 1711921466838888838 plattFirst_total_tLo

/-- The matching high carry of the opening indexed trace. -/
theorem plattFirst_indexed_tHi :
    let fuel := plattAlignedFirst.period *
      (plattAlignedFirst.rootCount + plattAlignedFirst.segCount)
    (squaredCombinedIndexedRun 0 plattAlignedFirst mobWideBits fuel
      (combinedEntry plattAlignedFirst plattFirstSeed)).regs rTHi = 32768 := by
  exact squaredComputation_total_tHi_to_indexed
    plattFirstComputation plattAlignedFirst mobWideBits plattFirstSeed
    plattFirst_program 32768 plattFirst_total_tHi

/-- Receipt result in the transparent residue-model projection consumed by
the production signal theorem. -/
theorem plattFirst_readRes_viol_zero :
    let fuel := plattAlignedFirst.period *
      (plattAlignedFirst.rootCount + plattAlignedFirst.segCount)
    (readRes (squaredCombinedIndexedRun 0 plattAlignedFirst mobWideBits fuel
      (combinedEntry plattAlignedFirst plattFirstSeed))).viol = 0 := by
  simpa only [combinedEntry, readRes, rMViol] using
    plattFirst_indexed_viol_zero

/-- Tail receipt result in the same transparent projection. -/
theorem plattTail_readRes_viol_zero :
    let fuel := plattAlignedTail.period *
      (plattAlignedTail.rootCount + plattAlignedTail.segCount)
    (readRes (squaredCombinedIndexedRun 0 plattAlignedTail mobWideBits fuel
      (combinedEntry plattAlignedTail plattTailSeed))).viol = 0 := by
  simpa only [combinedEntry, readRes, rMViol] using
    plattTail_indexed_viol_zero

end LeanCompCert.Ports.ArraySegMobiusPlattAuditTrace

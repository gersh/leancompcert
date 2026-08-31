import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceBodyCuts
import LeanCompCert.Ports.DirichletLadderExternalSafetyReferenceEarlyGates

/-! Exact three-cut source identity used by the acceptance telescope. -/

set_option autoImplicit false

namespace LeanCompCert.Ports.DirichletLadderExternalSafety

open LeanCompCert.Verified.ArrayState
open LeanCompCert.Ports.DirichletLadder

theorem historicalBody_eq_load_early_post (c : Cfg) :
    c.bodyBlock = historicalLoad c ++ historicalEarly c ++
      historicalPostEarly c := by
  rw [historicalBody_eq_four_cuts, historicalBodyPrefix_eq_cuts,
    historicalBodyFlags_eq_cuts, historicalBodyHeightCoverage_eq_cuts,
    historicalBodyTail_eq_cuts, historicalPostEarly_eq_source_parts]
  simp only [historicalMainFlags, historicalMiddleFlags,
    historicalHeightPrefix, historicalCoverageBlock,
    historicalCoveragePrefix, historicalOvershootBlock,
    historicalOvershootPrefix, historicalLateFlags, List.nil_append,
    List.append_assoc]

end LeanCompCert.Ports.DirichletLadderExternalSafety

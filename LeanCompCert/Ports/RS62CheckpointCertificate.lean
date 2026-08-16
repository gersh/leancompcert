import LeanCompCert.Ports.RS62CheckpointManifestData
import LeanCompCert.Ports.RS62SegmentedReceipt

/-!
# Physical certificate boundary for the RS62 checkpoint campaign

The single run admission below ranges only over the 120 literal rows in
`RS62CheckpointManifestData.rows`.  Each value is the exact seven-stage shared
memory trace emitted by `bench/RS62SegmentedPipelineEmit.lean`; it does not
admit the paper recurrence or a precomputed Boolean.

Configuration facts are deliberately separate.  They are finite arithmetic,
prime-table length, and marking-budget claims that will be supplied by a
compiled configuration checker.  Once supplied, `row_source_loopE` converts
the physical trace to the exact LeanCompCert source recurrence without
executing a checkpoint range in Lean.
-/

namespace LeanCompCert.Ports.RS62CheckpointCertificate

open LeanCompCert.Verified.Reflect
open LeanCompCert.Ports.ArraySegSieve
open LeanCompCert.Ports.ArraySegMobiusIndexedFull
open LeanCompCert.Ports.ArraySegMobiusIndexedRootMixed
open LeanCompCert.Ports.RS62CheckpointManifestData
open LeanCompCert.Ports.RS62SegmentedReceipt

/-- All non-execution premises of the generic segmented receipt theorem.
The fields are propositions, not Boolean carriers; the planned compiled
configuration program proves exactly this structure. -/
structure ConfigurationCertificate (row : Row)
    (bootBound valid delta : Nat) : Prop where
  schedule : SingleMixedPaddedRootSchedule row.cfg bootBound valid delta
  baseEq :
    (1 + ((row.cfg.segLen + delta) % M)) % M = row.cfg.lo
  tableLength :
    (rootScanMixed row.cfg.bootPrimes bootBound 1 valid).length =
      row.cfg.tableLen
  markBudget :
    ((rootScanMixed row.cfg.bootPrimes bootBound 1 valid).map
      fun p => row.cfg.segLen / p + 2).sum ≤ row.cfg.markSteps
  indexRoom : row.cfg.rootSpan + row.cfg.markSteps < M
  rootSquareRoom : row.cfg.rootCap * row.cfg.rootCap < M
  segmentRootRoom : row.cfg.segLen + row.cfg.rootCap < M
  endpointWordRoom : row.cfg.lo + row.cfg.segLen < M
  aboveRoot : row.cfg.rootCap < row.cfg.lo
  rootCoverage :
    row.cfg.lo + row.cfg.segLen - 1 ≤ row.cfg.rootCap * row.cfg.rootCap
  startAtLeastThree : 3 ≤ row.cfg.lo
  lowerWord : row.SL < M
  upperWord : row.SU < M
  endpointBound : row.cfg.lo + row.cfg.segLen ≤ 2 ^ 40
  arrayBytesRoom : 8 * row.cfg.arrayLen ≤ M

def HasConfigurationCertificate (row : Row) : Prop :=
  ∃ bootBound valid delta, ConfigurationCertificate row bootBound valid delta

/-- The actual memory-capped campaign returned the exact seven-stage trace for
each of the 120 manifest rows. -/
axiom rs62CheckpointCampaign_compcert_run (row : Row) (hrow : row ∈ rows) :
  SegmentReceipt row.cfg row.SL row.SU row.lower row.upper

/-- One compiled configuration certificate plus its retained physical trace
proves the exact source recurrence for that checkpoint segment. -/
theorem row_source_loopE (row : Row) (hrow : row ∈ rows)
    (hcfg : HasConfigurationCertificate row) :
    LeanCompCert.Ports.RS62.loopE
      RS62SegmentedPrimeMask.isPrimeBool row.cfg.segLen row.cfg.lo
      row.SL row.SU = (row.lower, row.upper) := by
  rcases hcfg with ⟨bootBound, valid, delta, hcfg⟩
  exact source_loopE_of_segmentReceipt row.cfg bootBound valid
    delta row.SL row.SU row.lower row.upper hcfg.schedule hcfg.baseEq
    hcfg.tableLength hcfg.markBudget hcfg.indexRoom hcfg.rootSquareRoom
    hcfg.segmentRootRoom hcfg.endpointWordRoom hcfg.aboveRoot
    hcfg.rootCoverage hcfg.startAtLeastThree hcfg.lowerWord hcfg.upperWord
    hcfg.endpointBound hcfg.arrayBytesRoom
    (rs62CheckpointCampaign_compcert_run row hrow)

#print axioms row_source_loopE

end LeanCompCert.Ports.RS62CheckpointCertificate

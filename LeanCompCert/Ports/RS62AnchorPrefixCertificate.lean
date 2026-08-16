import LeanCompCert.Ports.RS62LadderReceipt

/-!
# CompCert certificate for the small RS62 anchor prefix

The full anchor starts below the range where the segmented prime-mask program
can use its `rootCap < lo` invariant.  This certificate handles exactly the
small prefix `[101, 10001)` with the proved guarded scalar program.  The
980,100 trial-divisor rounds are executed only by the generated CompCert C;
Lean discharges the word bounds and connects the retained machine result to
the symbolic source recurrence.
-/

namespace LeanCompCert.Ports.RS62AnchorPrefixCertificate

open LeanCompCert
open LeanCompCert.Ports.RS62
open LeanCompCert.Ports.RS62Ladder
open LeanCompCert.Ports.RS62LadderEncoding
open LeanCompCert.Ports.RS62LadderReceipt

/-- Retained accepting CompCert result for `[101, 10001)`.  The benchmark
manifest records the emitted-C and executable hashes and the memory-capped
generation, compilation, and run measurements. -/
axiom rs62AnchorPrefix_compcert_run :
  SegmentReceipt 101 9900 99 0 0
    191722931109946 191728806920095

theorem prefix_flatRoom : FlatRoom 101 9900 99 0 0 :=
  flatRoom_of_endpoint_bounds 101 9900 99 0 0
    (by decide) (by decide) (by decide)

/-- Symbolic correctness of the guarded scalar encoding.  This proof does
not evaluate any candidate or divisor loop in Lean. -/
theorem prefix_encoding :
    LadderEncoding scanPrime 101 9900 99 0 0 :=
  ladderEncoding_scanPrime 101 9900 99 0 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    prefix_flatRoom

/-- Exact source recurrence certified by the compiled prefix run. -/
theorem prefix_loopE_scanPrime :
    loopE scanPrime 9900 101 0 0 =
      (191722931109946, 191728806920095) :=
  loopE_scanPrime_of_segmentReceipt
    101 9900 99 0 0 191722931109946 191728806920095
    prefix_encoding rs62AnchorPrefix_compcert_run

#print axioms prefix_loopE_scanPrime

end LeanCompCert.Ports.RS62AnchorPrefixCertificate

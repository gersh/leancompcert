import LeanCompCert.Testing.VerifiedDecide
import LeanCompCert.Testing.MertensCertificate
import LeanCompCert.Testing.WideMertensCertificate
import LeanCompCert.Testing.SquarefreeMertensCertificate
import LeanCompCert.Testing.ReflectedCertificate
import LeanCompCert.Testing.FixedPointCertificate
import LeanCompCert.Testing.PackedCoverageCertificate
import LeanCompCert.Verified.Limb
import LeanCompCert.Verified.EarlyExit
import LeanCompCert.Verified.Rolled
import LeanCompCert.Verified.GcdEquiv
import LeanCompCert.Verified.SqrtEquiv
import LeanCompCert.Verified.SignedLimb
import LeanCompCert.Verified.Log2Fixed
import LeanCompCert.Verified.Sieve
import LeanCompCert.Verified.Dyadic
import LeanCompCert.Verified.MulWide
import LeanCompCert.Verified.Frontend
import LeanCompCert.Verified.ArrayState
import LeanCompCert.Verified.MemFragment
import LeanCompCert.Verified.Packed
import LeanCompCert.Verified.PackedTransfer
import LeanCompCert.Verified.ListFold
import LeanCompCert.Verified.PackedSieve
import LeanCompCert.Verified.Segment
import LeanCompCert.Verified.FoldBridge
import LeanCompCert.Ports.RS62Increments
import LeanCompCert.Ports.RS62LoopE
import LeanCompCert.Ports.TGSieve
import LeanCompCert.Ports.TGLadder


/-!
Axiom-audit gate (M7): prints the axiom dependencies of every certificate
theorem. The acceptance script enforces an allowlist — it fails if any
axiom outside `propext`/`Classical.choice`/`Quot.sound` appears, which
covers the native-evaluation axioms (`ofReduceBool`/`ofReduceNat`,
`Lean.trustCompiler`) as well as `sorryAx` and bespoke axioms.

New certificates must be added to this list by hand; a misspelled name
fails elaboration, so an entry cannot silently audit nothing.
-/
#print axioms LeanCompCert.Verified.Computation.result_preserved
#print axioms LeanCompCert.Testing.VerifiedDecide.source_computation_returns_42
#print axioms LeanCompCert.Testing.MertensCertificate.referenceSum_eq
#print axioms LeanCompCert.Testing.WideMertensCertificate.referenceSum_eq
#print axioms LeanCompCert.Testing.SquarefreeMertensCertificate.referenceSum_eq
#print axioms LeanCompCert.Testing.ReflectedCertificate.referenceSum_eq
#print axioms LeanCompCert.Testing.FixedPointCertificate.referenceSum_eq
#print axioms LeanCompCert.Verified.Reflect.Program.evalCC_compile
#print axioms LeanCompCert.Verified.Reflect.toComputation_returns
#print axioms LeanCompCert.Verified.Packed.lane_poke_self
#print axioms LeanCompCert.Verified.Packed.lane_poke_ne
#print axioms LeanCompCert.Verified.Packed.lane_lt
#print axioms LeanCompCert.Verified.Packed.laneState_poke
#print axioms LeanCompCert.Verified.Packed.testBit_repunit
#print axioms LeanCompCert.Verified.Packed.testBit_classMask
#print axioms LeanCompCert.Verified.Packed.testBit_orAll
#print axioms LeanCompCert.Verified.Packed.covers_iff
#print axioms LeanCompCert.Verified.Packed.mem_class_of_covers_classUnion
#print axioms LeanCompCert.Verified.Packed.laneState_poke_eq_set
#print axioms LeanCompCert.Verified.Packed.denoteInstrsPacked_eq
#print axioms LeanCompCert.Verified.Packed.Program.denotePacked_eq_denote
#print axioms LeanCompCert.Verified.Packed.arrState_poke_eq_writeArr
#print axioms LeanCompCert.Verified.ListFold.foldl_guard
#print axioms LeanCompCert.Verified.ListFold.foldl_table
#print axioms LeanCompCert.Verified.ListFold.foldl_of_certifies
#print axioms LeanCompCert.Verified.ListFold.evalCCSequence_foldTraceList
#print axioms LeanCompCert.Verified.ListFold.LProgram.evalCC_compile
#print axioms LeanCompCert.Testing.PackedCoverageCertificate.coverage_accepted
#print axioms LeanCompCert.Testing.PackedCoverageCertificate.covering_system_covers
#print axioms LeanCompCert.Verified.PackedSieve.exists_prime_dvd
#print axioms LeanCompCert.Verified.PackedSieve.exists_prime_factor_le_sqrt
#print axioms LeanCompCert.Verified.PackedSieve.isPrime_iff_bounded
#print axioms LeanCompCert.Verified.PackedSieve.testBit_multiplesMask
#print axioms LeanCompCert.Verified.PackedSieve.testBit_compositeBits
#print axioms LeanCompCert.Verified.PackedSieve.testBit_compositeBits_eq_false_iff
#print axioms LeanCompCert.Verified.PackedSieve.sieveList_eq_filter
#print axioms LeanCompCert.Verified.PackedSieve.PrimeBase.step
#print axioms LeanCompCert.Verified.PackedSieve.PrimeBase.ofTrialDivision
#print axioms LeanCompCert.Verified.Limb.mulLimbs_val
#print axioms LeanCompCert.Verified.EarlyExit.foldP_accepts_iff
#print axioms LeanCompCert.Verified.Reflect.evalCCSequence_var_eq_lit
#print axioms LeanCompCert.Verified.Reflect.lit_preserves_counter
#print axioms LeanCompCert.Verified.Limb.divModMSB_val
#print axioms LeanCompCert.Verified.Reflect.rolledTrace_eq_augmented
#print axioms LeanCompCert.Verified.Gcd.gcdFuel_eq
#print axioms LeanCompCert.Verified.SqrtEquiv.isqrt_eq
#print axioms LeanCompCert.Verified.SignedLimb.add_val
#print axioms LeanCompCert.Verified.Log2Fixed.log2Fixed_eq
#print axioms LeanCompCert.Verified.Sieve.spfFixed_eq_leastFactor
#print axioms LeanCompCert.Verified.Dyadic.mulLo_le
#print axioms LeanCompCert.Verified.MulWide.hl_spec
#print axioms LeanCompCert.Verified.Frontend.compileExpr_correct
#print axioms LeanCompCert.Verified.ArrayState.sieveSweep_cell
#print axioms LeanCompCert.Verified.MemFragment.lowerMSequence_correct

-- Generic segmentation lever
#print axioms LeanCompCert.Verified.Segment.foldl_range'_split
#print axioms LeanCompCert.Verified.Segment.foldl_range'_of_chain
#print axioms LeanCompCert.Verified.Segment.foldl_range_of_chain
-- Generic program/fold bridge
#print axioms LeanCompCert.Verified.FoldBridge.foldlM_body_eq_foldl
#print axioms LeanCompCert.Verified.FoldBridge.foldl_obs
#print axioms LeanCompCert.Verified.FoldBridge.LProgram.denote_eq_foldl
#print axioms LeanCompCert.Verified.FoldBridge.Program.denote_eq_foldl
#print axioms LeanCompCert.Verified.FoldBridge.Program.denote_eq_scalar_foldl
-- RS62 ladder port
#print axioms LeanCompCert.Ports.RS62.div_sub_eq_sub_ceilDiv
#print axioms LeanCompCert.Ports.RS62.incL_eq_wordSafe
#print axioms LeanCompCert.Ports.RS62.incU_eq_wordSafe
#print axioms LeanCompCert.Ports.RS62.loopE_eq_foldl
#print axioms LeanCompCert.Ports.RS62.loopE_of_chain
#print axioms LeanCompCert.Ports.RS62.loopE_eq_filter_foldl
#print axioms LeanCompCert.Ports.RS62.loopE_eq_word

-- Helfgott--Platt Goldbach ladder port: stage (a), the progression sieve
#print axioms LeanCompCert.Ports.TGSieve.dvd_of_odd_dvd_two_mul
#print axioms LeanCompCert.Ports.TGSieve.dvd_of_odd_dvd_two_pow_mul
#print axioms LeanCompCert.Ports.TGSieve.dvd_proth_iff
#print axioms LeanCompCert.Ports.TGSieve.sieveTable_valid
#print axioms LeanCompCert.Ports.TGSieve.hitCount_eq_zero_iff
#print axioms LeanCompCert.Ports.TGSieve.bodyInstrs_wf
#print axioms LeanCompCert.Ports.TGSieve.sieveProgram_wf
#print axioms LeanCompCert.Ports.TGSieve.sieveProgram_denote_mod
#print axioms LeanCompCert.Ports.TGSieve.sieveProgram_denote
-- stage (c), ladder assembly
#print axioms LeanCompCert.Ports.TGLadder.gap_le_iff
#print axioms LeanCompCert.Ports.TGLadder.covers
#print axioms LeanCompCert.Ports.TGLadder.lastNum_runningK
#print axioms LeanCompCert.Ports.TGLadder.gapChain_of_deltas
#print axioms LeanCompCert.Ports.TGLadder.covers_of_deltas
#print axioms LeanCompCert.Ports.TGLadder.finalK_eq
#print axioms LeanCompCert.Ports.TGLadder.ladderProgram_wf
#print axioms LeanCompCert.Ports.TGLadder.ladderProgram_denote_mod
#print axioms LeanCompCert.Ports.TGLadder.ladderProgram_denote
#print axioms LeanCompCert.Ports.TGLadder.covers_of_accepts

import LeanCompCert.Testing.VerifiedDecide
import LeanCompCert.Testing.MertensCertificate
import LeanCompCert.Testing.WideMertensCertificate
import LeanCompCert.Testing.SquarefreeMertensCertificate
import LeanCompCert.Testing.ReflectedCertificate
import LeanCompCert.Testing.FixedPointCertificate
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
